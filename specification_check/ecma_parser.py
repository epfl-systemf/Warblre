from dataclasses import dataclass
from typing import Dict, List

import bs4
import requests
from bs4 import BeautifulSoup, PageElement
from spec_merger.content_classes.dictionary import Dictionary
from spec_merger.content_classes.string import String
from spec_merger.aligner_utils import Position
from spec_merger.utils import ParserState, ParsedPage, Parser


@dataclass(frozen=True)
class URLPosition(Position):
    url: str

    def html_str(self):
        return f"<a href='{self.url}'>{self.url}</a>"


def add_case(cases: dict[str, Dictionary], case: tuple[str, String], key: str):
    # lines = OrderedSeq(case[1].position, list(map(lambda x: String(None,x),case[1].value.split("\n"))))
    if cases.get(key) is not None:
        cases[key].entries[case[0]] = case[1]
    else:
        cases[key] = Dictionary(None, {case[0]: case[1]})


class ECMAParser(Parser):

    def __init__(self, url, parser_name="ECMA", sections=None):
        self.name = parser_name
        if sections is None:
            sections = ["sec-regexp-regular-expression-objects"]
        self.sections = sections
        self.url = url
        self.page = self.__get_page()
        self.sections_by_number: Dict[str, Dictionary] = None
        self.avoid = {None, "emu-note", "\n"}

    def __get_page(self):
        html_spec = requests.get(self.url).content
        soup = BeautifulSoup(html_spec, 'html.parser')
        return soup

    def __parse_section(self, section_html: BeautifulSoup, sections_by_number: Dict[str, Dictionary]):
        position = URLPosition(self.url + "#" + section_html.get("id"))
        title = section_html.find("h1").find("span", {"class": "secnum"}).text
        first_subsection = section_html.find("emu-clause")
        if first_subsection is not None:
            paragraph = [x for x in first_subsection.previous_siblings if x.name not in self.avoid][::-1]
            sections_by_number[title] = self.__parse_subsection(paragraph, position)
            for new_section in section_html.find_all("emu-clause", recursive=False):
                self.__parse_section(new_section, sections_by_number)
        else:
            paragraph = [x for x in section_html.children if x.name not in self.avoid]
            sections_by_number[title] = self.__parse_subsection(paragraph, position)

    def __preprocess(self, sections):
        sections_by_numbers = {}
        for section in sections:
            html_section = self.page.find("emu-clause", {"id": section})
            self.__parse_section(html_section, sections_by_numbers)
        self.sections_by_number = sections_by_numbers

    @staticmethod
    def __strip_sides(string: str) -> str:
        return string.replace("\n", "").replace("\t", "").lstrip().rstrip()

    def __parse_list(self, ol_or_ul: BeautifulSoup, list_type: str = "ol", prefix: str = "") -> str:
        result = ""
        for li in ol_or_ul.children:
            if li == '\n':
                continue
            if (sub_list := li.find(list_type)) is not None:
                result += prefix + "".join(
                    [self.__strip_sides(self.__parse_p(x)) for x in sub_list.previous_siblings][::-1]) + "\n"
                result += self.__parse_list(sub_list, list_type)
            else:
                result += prefix + self.__strip_sides(self.__parse_p(li)) + "\n"

        return result

    def __parse_emu_alg(self, emu_alg_section: BeautifulSoup) -> str:
        # An emu-alg always contain a single <ol> containing a lot of <li> elements and can also contain other <ol>
        # elements
        main_ol = list(emu_alg_section.children)[0]
        return self.__parse_list(main_ol)

    def __parse_emu_mods(self, mods: PageElement):
        match list(mods.children)[0]:
            case "emu-opt":
                return "_" + mods.text
            case _:
                return mods.text

    def __parse_emu_grammar(self, emu_grammar_section: BeautifulSoup) -> list[list[str]]:
        # an emu-grammar always contains one or multiple emu-production which themselves contain :
        # - an emu-nt
        # - an emu-geq
        # one or multiple emu-rhs which all contain one or more element
        emu_prods = emu_grammar_section.find_all("emu-production")
        result = []
        for prod in emu_prods:
            tmp = ["", ""]
            tmp[0] = prod.find("emu-nt").text
            separator = " " if prod.has_attr("collapsed") else "\n"
            right_hand_sides = prod.find_all("emu-rhs", recursive=False)
            for rhs in right_hand_sides:
                # hack to avoid beautiful soup to add \n for no reason ?
                if type(rhs) is bs4.NavigableString:
                    continue
                tmp[1] += separator
                to_add = ""
                for nt in rhs.children:
                    if type(nt) is bs4.NavigableString:
                        continue
                    for small_child in nt.children:
                        if small_child.name == "emu-mods":
                            to_add += "_" + self.__parse_emu_mods(small_child)
                        else:
                            to_add += small_child.text
                    to_add = to_add + " " if to_add != "" else ""
                # remove last space
                if to_add[-1] == " ":
                    to_add = to_add[:-1]
                tmp[1] += to_add
            result.append(tmp)
        return result

    def __parse_p(self, p: BeautifulSoup):
        res = ""
        if type(p) is bs4.NavigableString:
            return p.text
        for child in p.children:
            match child.name:
                case "emu-grammar":
                    res += " ::".join(f"{x[0]} ::{x[1]}" for x in self.__parse_emu_grammar(child))
                case "sup":
                    res += "^" + child.text
                case _:
                    res += child.text
        return res

    def __parse_subsection(self, subsection: List[BeautifulSoup], position: URLPosition) -> Dictionary:
        title = ""
        description = ""
        cases: dict[str, Dictionary] = {}
        current_case = ""
        current_case_titles = [["", ""]]
        parser_state = ParserState.READING_TITLE
        for children in subsection:
            match children.name:
                case "h1":
                    title += self.__strip_sides(children.text)
                    parser_state = ParserState.READING_DESCRIPTION
                case "p":
                    if parser_state in {ParserState.READING_TITLE, ParserState.READING_DESCRIPTION}:
                        parser_state = ParserState.READING_DESCRIPTION
                        description += self.__strip_sides(self.__parse_p(children)) + " "
                    else:
                        pass
                case "ul":
                    match parser_state:
                        case ParserState.READING_TITLE:
                            title += self.__strip_sides(children.text) + " "
                        case ParserState.READING_DESCRIPTION:
                            description += self.__parse_list(children, "ul", prefix=" ")
                        case ParserState.READING_CASES:
                            current_case += self.__parse_list(children, "ul", prefix="* ")
                case "emu-alg":
                    parser_state = ParserState.READING_CASES
                    current_case += self.__parse_emu_alg(children)
                    for current_case_title in current_case_titles:
                        add_case(cases, (current_case_title[1], String(position, current_case)), current_case_title[0])
                    current_case = ""
                    current_case_titles = [["", ""]]
                case "emu-grammar":
                    parser_state = ParserState.READING_CASES
                    if current_case != "":
                        for current_case_title in current_case_titles:
                            add_case(cases, (current_case_title[1], String(position, current_case)),
                                     current_case_title[0])
                        current_case = ""
                    current_case_titles = self.__parse_emu_grammar(children)
                case "span" | "emu-table" | "emu-import" | "h2" | "emu-table":
                    pass
                case _:
                    print(f"ERROR: Unhandled tag in html section : {children.name}, {children.text}")
                    raise ValueError
        if current_case_titles != [["", ""]]:
            for case_title in current_case_titles:
                add_case(cases, (case_title[1], String(position, current_case)), case_title[0])
        return Dictionary(position, {"title": String(None, title),
                                      "description": String(None, description),
                                      "cases": Dictionary(None, cases)})

    def get_parsed_page(self) -> ParsedPage:
        if self.sections_by_number is None:
            self.__preprocess(self.sections)
        return ParsedPage(self.name, Dictionary(None, self.sections_by_number))
