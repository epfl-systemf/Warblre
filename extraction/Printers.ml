module Printer(E: Encoding.Character) = struct
  open Extracted.Patterns

  type character = E.character
  module CS = Set.Make(Int)

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
      | AtomEsc (GroupEsc name) -> "\\" ^ "k<" ^ name ^ ">"
      | Disjunction (r1, r2) -> prio ((iter r1 (next 0)) ^ "|" ^ (iter r2 0)) 0 current
      | Quantified (r1, q) -> prio ((iter r1 4) ^ quantifier_to_string q) 3 current
      | Seq (r1, r2) -> prio ((iter r1 (next 1)) ^ (iter r2 1)) 1 current
      | Group (None, r1) -> "(" ^ iter r1 0 ^ ")"
      | Group (Some name, r1) -> "(?<" ^ name ^  ">" ^ iter r1 0 ^ ")"
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
end

module Utf16Printer = Printer(Encoding.Utf16)
module UnicodePrinter = Printer(Encoding.Unicode)