module Printer(E: Encoding.Character) = struct
  open Extracted.Patterns
  open Extracted.Notation

  type character = E.character

  module Internal = struct
    module CS = Set.Make(Int)

    (* Regex printers *)

    let prio (s: string) (at: int) (current: int) : string =
      if at < current then "(?:" ^ s ^ ")" else s

    (* TODO: check spec and update list *)
    let escaped = CS.of_list (List.map Char.code ('\\' :: '/' :: '-' :: '[' :: ']' :: '{' :: '}' :: '(' :: ')' :: '*' :: '+' :: '?' :: '$' :: '^' :: '|' :: '.' :: []))

    let escape (c: character) : string =
      let str = E.list_to_string (c :: []) in
      if String.length str != 1 then
        failwith "Unexpected escape corner case: '" ^ str ^ "'"
      else
        "\\" ^ str

    let char_lit_to_string (c: character) : string =
      let i = E.char_to_int c in
      if CS.mem i escaped then
        escape c
      else
        let str = E.list_to_string (c :: []) in
        str

    let hex4digits_to_string (h: Extracted.HexDigit.coq_Hex4Digits) : string =
      let Coq_hex4 (h1, h2, h3, h4) = h in
      (String.make 1 h1) ^ (String.make 1 h2) ^ (String.make 1 h3) ^ (String.make 1 h4)

    let character_escape_to_string (esc: character coq_CharacterEscape) : string =
      match esc with
      | ControlEsc esc -> (match esc with
        | Coq_esc_f -> "\\f"
        | Coq_esc_n -> "\\n"
        | Coq_esc_r -> "\\r"
        | Coq_esc_t -> "\\t"
        | Coq_esc_v -> "\\v")
      | AsciiControlEsc c -> "\\c" ^ (String.make 1 c)
      | Coq_esc_Zero -> "\\0"
      | HexEscape (h1, h2) -> "\\x" ^ (String.make 1 h1) ^ (String.make 1 h2)
      | UnicodeEsc esc -> (match esc with
        | Pair (h1, h2) -> "\\u{" ^ (hex4digits_to_string h1) ^ "}\\u{" ^ (hex4digits_to_string h2) ^ "}"
        | Lonely h -> "\\u{" ^ (hex4digits_to_string h) ^ "}"
        | CodePoint i -> failwith "TODO: pretty-printer -- \\u{codepoint}")
      | IdentityEsc c -> escape c

    let character_class_escape_to_string (esc: character coq_CharacterClassEscape) : string =
      match esc with
      | Coq_esc_d -> "\\d"
      | Coq_esc_D -> "\\D"
      | Coq_esc_s -> "\\s"
      | Coq_esc_S -> "\\S"
      | Coq_esc_w -> "\\w"
      | Coq_esc_W -> "\\W"
      | UnicodeProp _ -> "\\p{...}"
      | UnicodePropNeg _ -> "\\P{...}"

    let quantifier_prefix_to_string (qp: coq_QuantifierPrefix) : string =
      match qp with
      | Star -> "*"
      | Plus -> "+"
      | Question -> "?"
      | RepExact (i) -> "{" ^ string_of_int i ^ "}"
      | RepPartialRange (i) -> "{" ^ string_of_int i ^ ",}"
      | RepRange (imin,imax) -> "{" ^ string_of_int imin ^ "," ^ string_of_int imax ^ "}"

    let quantifier_to_string (q: coq_Quantifier) : string =
      match q with
      | Greedy (qp) -> quantifier_prefix_to_string qp
      | Lazy (qp) -> quantifier_prefix_to_string qp ^ "?"

    let class_atom_to_string (ca: character coq_ClassAtom) : string =
      match ca with
      | SourceCharacter c -> char_lit_to_string c
      | ClassEsc Coq_esc_b -> "\\b"
      | ClassEsc Coq_esc_Dash -> "\\-"
      | ClassEsc (CCharacterClassEsc esc) -> character_class_escape_to_string esc
      | ClassEsc (CCharacterEsc esc) -> character_escape_to_string esc

    let rec range_to_string (r: character coq_ClassRanges) : string =
    match r with
    | EmptyCR -> ""
    | ClassAtomCR (ca, r) -> (class_atom_to_string ca) ^ (range_to_string r)
    | RangeCR (l, h, r) -> (class_atom_to_string l) ^ "-" ^ (class_atom_to_string h) ^ (range_to_string r)


    (* Exec result printers *)

    let quoted (str: Unsigned.uint16 list) : string = "'" ^ Encoding.Utf16.list_to_string str ^ "'"

    let string_range (string_input: string) (single_capture: CaptureRange.coq_type) : string =
      let { CaptureRange.startIndex = s; CaptureRange.endIndex = e } = single_capture in
      String.sub string_input s (e-s)

    let option_to_string (type a) ?(none="Undefined") ?(some_prefix="") (p: a -> string) (o: a option) : string =
      match o with
      | None -> none
      | Some l -> some_prefix ^ p l

    let pair_to_string (type a b) ?(start="(") ?(sep=",") ?(endd=")") (pa: a -> string) (pb: b -> string) (t: (a * b)) : string =
      let (i1, i2) = t in
      start ^ pa i1 ^ sep ^ pb i2 ^ endd

    let keyed_list_to_string (type a b) ?(prefix="\t#") ?(key_sep=":") ?(sep=" ") (pa: a -> string) (pb: b -> string) (l: (a * b) list) : string =
      if List.length l = 0 then "[]" else
      prefix ^ String.concat sep (List.map (fun (k, v) -> pa k ^ key_sep ^ pb v) l)

    let indexed_list_to_string (type a) ?(prefix="") ?(key_sep=":") ?(sep=" ") (p: a -> string) (l: a list) : string =
      let rec indexed (l: a list) (index: int) : (int * a) list =
        match l with
        | [] -> []
        | h :: t -> (index, h) :: (indexed t (index + 1))
      in
      keyed_list_to_string ~prefix:prefix ~key_sep:key_sep ~sep:sep string_of_int p (indexed l 0)

    let exec_array_exotic_to_string (a: Extracted.ExecArrayExotic.coq_type) : string =
      let zip_with_opt (type a b) (l: a list) (r: b option list option) = match r with
        | None -> List.map (fun l -> (l, None)) l
        | Some r -> List.combine l r
      in
      let named_captures: ('a * ('a option * (int * int) option)) list option =
        Option.map (fun l ->
          List.map (fun ((n, l), r) -> (n, (l, r))) (zip_with_opt l (Option.map (List.map snd) a.indices_groups))
        ) a.groups
      in
      String.concat "\n" (List.filter (fun s -> String.length s != 0) (
        ("Start:" ^ "\027[20G" ^ string_of_int a.index) ::
        ("Captures:" ^ (
          indexed_list_to_string ~prefix:"\027[20G# " ~key_sep:"\027[32G: " ~sep:"\n\027[20G# " (
            pair_to_string ~start:"" ~sep:"\027[64G" ~endd:"" (
              option_to_string quoted) (
              option_to_string ~none:"" (pair_to_string string_of_int string_of_int))))
          (zip_with_opt a.array a.indices_array)) ::
        (option_to_string ~none:"" ~some_prefix:"Named captures:"
            (keyed_list_to_string ~prefix:"\027[20G# " ~key_sep:"\027[32G: " ~sep:"\n\027[20G# "
              Encoding.Utf16.list_to_string
              (pair_to_string ~start:"" ~sep:"\027[64G" ~endd:""
                (option_to_string quoted)
                (option_to_string ~none:"" (pair_to_string string_of_int string_of_int))))
          named_captures) ::
        []
      ))
  end
  open Internal

  (*  With delimited=false, the delimiters (/.../) won't be printed.
    In strict mode, the regex will be printed as is.
    In non-strict mode, an equivalent regex (through associativity) might be printed. *)
  let regex_to_string ?(delimited=true) ?(strict=false) (r: character coq_Regex) : string =
    let next (i: int) : int = if strict then i + 1 else i in
    let rec iter (r: character coq_Regex) (current: int) : string =
      match r with
      | Empty -> ""
      | Char c -> char_lit_to_string c
      | Dot -> String.make 1 '.'
      | CharacterClass cc -> (match cc with
        | NoninvertedCC r -> "[" ^ (range_to_string r) ^ "]"
        | InvertedCC r -> "[^" ^ (range_to_string r) ^ "]")
      | AtomEsc (DecimalEsc gid) -> "\\" ^ string_of_int gid
      | AtomEsc (ACharacterClassEsc esc) -> character_class_escape_to_string esc
      | AtomEsc (ACharacterEsc esc) -> character_escape_to_string esc
      | AtomEsc (GroupEsc name) -> "\\" ^ "k<" ^ Encoding.Utf16.list_to_string name ^ ">"
      | Disjunction (r1, r2) -> prio ((iter r1 (next 0)) ^ "|" ^ (iter r2 0)) 0 current
      | Quantified (r1, q) -> prio ((iter r1 4) ^ quantifier_to_string q) 3 current
      | Seq (r1, r2) -> prio ((iter r1 (next 1)) ^ (iter r2 1)) 1 current
      | Group (None, r1) -> "(" ^ iter r1 0 ^ ")"
      | Group (Some name, r1) -> "(?<" ^ Encoding.Utf16.list_to_string name ^  ">" ^ iter r1 0 ^ ")"
      | InputStart -> "^"
      | InputEnd -> "$"
      | WordBoundary -> "\\b"
      | NotWordBoundary -> "\\B"
      | Lookahead (r1) -> "(?=" ^ iter r1 0 ^ ")"
      | NegativeLookahead (r1) -> "(?!" ^ iter r1 0 ^ ")"
      | Lookbehind (r1) -> "(?<=" ^ iter r1 0 ^ ")"
      | NegativeLookbehind (r1) -> "(?<!" ^ iter r1 0 ^ ")"
    in
    let res = iter r 0 in
    if delimited then "/" ^ res ^ "/" else res

  let exec_result_to_string (r: character Extracted.execResult) : string =
    match r with
    | Null _ -> "No Match"
    | Exotic (a, _) -> Internal.exec_array_exotic_to_string a
end

module Utf16Printer = Printer(Encoding.Utf16)
module UnicodePrinter = Printer(Encoding.Unicode)