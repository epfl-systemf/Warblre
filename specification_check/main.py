from spec_merger.aligner import Aligner
from coq_parser import COQParser
from ecma_parser import ECMAParser
from spec_merger.utils import Path


def main():
    paths = [Path("../mechanization/spec/", True)]
    files_to_exclude = [Path("../mechanization/spec/Node.v", False)]
    url = "https://262.ecma-international.org/14.0/"

    coq_parser = COQParser(paths, files_to_exclude)
    coq_parsed_page = coq_parser.get_parsed_page()
    ecma_parser_v14 = ECMAParser(url, parser_name="ECMAScript v14.0")
    ecma_parsed_page_v14 = ecma_parser_v14.get_parsed_page()

    a = Aligner()
    result = a.align(coq_parsed_page.entries, ecma_parsed_page_v14.entries)
    text_result = result.to_text()
    print(text_result, end="")


if __name__ == "__main__":
    main()
