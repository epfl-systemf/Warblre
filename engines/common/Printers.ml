open Engines
open Patterns

(* Prints regexes (and friends) in string format *)
module Printer(P: EngineParameters) (S: Encoding.StringLike with type t := P.string) = struct
  type ocaml_string = string
  module E = Engine(P)

  (* Internal printer combinators, used by the public ones. *)
  module Internal = struct
    module CS = Set.Make(Int)

    (* Regex printers *)

    let prio (s: ocaml_string) (at: int) (current: int) : ocaml_string =
      if at < current then "(?:" ^ s ^ ")" else s

    (* TODO: check spec and update list *)
    let escaped = CS.of_list (List.map Char.code ('\\' :: '/' :: '-' :: '[' :: ']' :: '{' :: '}' :: '(' :: ')' :: '*' :: '+' :: '?' :: '$' :: '^' :: '|' :: '.' :: []))

    let escape (c: P.character) : ocaml_string =
      let str = S.to_string (P.String.list_to_string (c :: [])) in
      if String.length str != 1 then
        failwith "Unexpected escape corner case: '" ^ str ^ "'"
      else
        "\\" ^ str

    let char_lit_to_string (c: P.character) : ocaml_string =
      let i = P.Character.numeric_value c in
      if CS.mem (BigInt.to_int i) escaped then
        escape c
      else
        let str = S.to_string (P.String.list_to_string (c :: [])) in
        str

    let hex_to_string (h: Extracted.HexDigit.coq_type) : ocaml_string =
      match h with
      | Zero -> "0"
      | One -> "1"
      | Two -> "2"
      | Three -> "3"
      | Four -> "4"
      | Five -> "5"
      | Six -> "6"
      | Seven -> "7"
      | Eight -> "8"
      | Nine -> "9"
      | A -> "A"
      | B -> "B"
      | C -> "C"
      | D -> "D"
      | E -> "E"
      | F -> "F"

    let ascii_letter_to_char (l: Extracted.AsciiLetter.coq_type) : char =
      match l with
      | Coq_a -> 'a'  
      | Coq_b -> 'b' 
      | Coq_c -> 'c' 
      | Coq_d -> 'd' 
      | Coq_e -> 'e' 
      | Coq_f -> 'f' 
      | Coq_g -> 'g' 
      | Coq_h -> 'h' 
      | Coq_i -> 'i' 
      | Coq_j -> 'j' 
      | Coq_k -> 'k' 
      | Coq_l -> 'l' 
      | Coq_m -> 'm' 
      | Coq_n -> 'n' 
      | Coq_o -> 'o' 
      | Coq_p -> 'p' 
      | Coq_q -> 'q' 
      | Coq_r -> 'r' 
      | Coq_s -> 's' 
      | Coq_t -> 't' 
      | Coq_u -> 'u' 
      | Coq_v -> 'v' 
      | Coq_w -> 'w' 
      | Coq_x -> 'x' 
      | Coq_y -> 'y' 
      | Coq_z -> 'z' 
      | A -> 'A' 
      | B -> 'B' 
      | C -> 'C' 
      | D -> 'D' 
      | E -> 'E' 
      | F -> 'F' 
      | G -> 'G' 
      | H -> 'H' 
      | I -> 'I' 
      | J -> 'J' 
      | K -> 'K' 
      | L -> 'L' 
      | M -> 'M' 
      | N -> 'N' 
      | O -> 'O' 
      | P -> 'P' 
      | Q -> 'Q' 
      | R -> 'R' 
      | S -> 'S' 
      | T -> 'T' 
      | U -> 'U' 
      | V -> 'V' 
      | W -> 'W' 
      | X -> 'X' 
      | Y -> 'Y' 
      | Z -> 'Z' 

    let hex4digits_to_string (h: Extracted.HexDigit.coq_Hex4Digits) : ocaml_string =
      let Coq_hex4 (h1, h2, h3, h4) = h in
      (hex_to_string h1) ^ (hex_to_string h2) ^ (hex_to_string h3) ^ (hex_to_string h4)

    let character_escape_to_string (esc: (P.character) coq_CharacterEscape) : ocaml_string =
      match esc with
      | ControlEsc esc -> (match esc with
        | Coq_esc_f -> "\\f"
        | Coq_esc_n -> "\\n"
        | Coq_esc_r -> "\\r"
        | Coq_esc_t -> "\\t"
        | Coq_esc_v -> "\\v")
      | AsciiControlEsc c -> "\\c" ^ (String.make 1 (ascii_letter_to_char c))
      | Coq_esc_Zero -> "\\0"
      | HexEscape (h1, h2) -> "\\x" ^ (hex_to_string h1) ^ (hex_to_string h2)
      | UnicodeEsc esc -> (match esc with
        | Pair (h1, h2) -> "\\u{" ^ (hex4digits_to_string h1) ^ "}\\u{" ^ (hex4digits_to_string h2) ^ "}"
        | Lonely h -> "\\u{" ^ (hex4digits_to_string h) ^ "}"
        | CodePoint _ -> failwith "TODO: pretty-printer -- \\u{codepoint}")
      | IdentityEsc c -> escape c

    let character_class_escape_to_string (esc: (P.property) coq_CharacterClassEscape) : ocaml_string =
      match esc with
      | Coq_esc_d -> "\\d"
      | Coq_esc_D -> "\\D"
      | Coq_esc_s -> "\\s"
      | Coq_esc_S -> "\\S"
      | Coq_esc_w -> "\\w"
      | Coq_esc_W -> "\\W"
      | UnicodeProp _ -> "\\p{...}"
      | UnicodePropNeg _ -> "\\P{...}"

    let quantifier_prefix_to_string (qp: coq_QuantifierPrefix) : ocaml_string =
      match qp with
      | Star -> "*"
      | Plus -> "+"
      | Question -> "?"
      | RepExact (i) -> "{" ^ BigInt.to_string i ^ "}"
      | RepPartialRange (i) -> "{" ^ BigInt.to_string i ^ ",}"
      | RepRange (imin,imax) -> "{" ^ BigInt.to_string imin ^ "," ^ BigInt.to_string imax ^ "}"

    let quantifier_to_string (q: coq_Quantifier) : ocaml_string =
      match q with
      | Greedy (qp) -> quantifier_prefix_to_string qp
      | Lazy (qp) -> quantifier_prefix_to_string qp ^ "?"

    let class_atom_to_string (ca: (P.character, P.property) coq_ClassAtom) : ocaml_string =
      match ca with
      | SourceCharacter c -> char_lit_to_string c
      | ClassEsc Coq_esc_b -> "\\b"
      | ClassEsc Coq_esc_Dash -> "\\-"
      | ClassEsc (CCharacterClassEsc esc) -> character_class_escape_to_string esc
      | ClassEsc (CCharacterEsc esc) -> character_escape_to_string esc

    let rec range_to_string (r: (P.character, P.property) coq_ClassRanges) : ocaml_string =
    match r with
    | EmptyCR -> ""
    | ClassAtomCR (ca, r) -> (class_atom_to_string ca) ^ (range_to_string r)
    | RangeCR (l, h, r) -> (class_atom_to_string l) ^ "-" ^ (class_atom_to_string h) ^ (range_to_string r)


    (* Exec result printers *)

    let quoted (str: P.string) : ocaml_string = "'" ^ S.to_string str ^ "'"

    let string_range (string_input: ocaml_string) (single_capture: Extracted.Notation.CaptureRange.coq_type) : ocaml_string =
      let { Extracted.Notation.CaptureRange.startIndex = s; Extracted.Notation.CaptureRange.endIndex = e } = single_capture in
      String.sub string_input (BigInt.to_int s) (BigInt.to_int (BigInt.sub e s))

    let option_to_string (type a) ?(none="Undefined") ?(some_prefix="") (p: a -> ocaml_string) (o: a option) : ocaml_string =
      match o with
      | None -> none
      | Some l -> some_prefix ^ p l

    let pair_to_string (type a b) ?(start="(") ?(sep=",") ?(endd=")") (pa: a -> ocaml_string) (pb: b -> ocaml_string) (t: (a * b)) : ocaml_string =
      let (i1, i2) = t in
      start ^ pa i1 ^ sep ^ pb i2 ^ endd

    let keyed_list_to_string (type a b) ?(nil="[]") ?(prefix="\t#") ?(key_sep=":") ?(sep=" ") (pa: a -> ocaml_string) (pb: b -> ocaml_string) (l: (a * b) list) : ocaml_string =
      if List.length l = 0 then nil else
      prefix ^ String.concat sep (List.map (fun (k, v) -> pa k ^ key_sep ^ pb v) l)

    let indexed_list_to_string (type a) ?(nil="[]") ?(prefix="") ?(key_sep=":") ?(sep=" ") (p: a -> ocaml_string) (l: a list) : ocaml_string =
      let rec indexed (l: a list) (index: BigInt.t) : (BigInt.t * a) list =
        match l with
        | [] -> []
        | h :: t -> (index, h) :: (indexed t (BigInt.Nat.succ index))
      in
      keyed_list_to_string ~nil:nil ~prefix:prefix ~key_sep:key_sep ~sep:sep BigInt.to_string p (indexed l (BigInt.of_int 0))

    let exec_array_exotic_to_string (pretty: bool) (a: E.execArrayExotic) : ocaml_string =
      if pretty then
        let zip_with_opt (type a b) (l: a list) (r: b option list option) = match r with
          | None -> List.map (fun l -> (l, None)) l
          | Some r -> List.combine l r
        in
        let named_captures: ('a * ('a option * (BigInt.t * BigInt.t) option)) list option =
          Option.map (fun l ->
            List.map (fun ((n, l), r) -> (n, (l, r))) (zip_with_opt l (Option.map (List.map snd) a.indices_groups))
          ) a.groups
        in
        String.concat "\n" (List.filter (fun s -> String.length s != 0) (
          ("Start:" ^ "\027[20G" ^ BigInt.to_string a.index) ::
          ("Captures:" ^ (
            indexed_list_to_string ~prefix:"\027[20G# " ~key_sep:"\027[32G: " ~sep:"\n\027[20G# " (
              pair_to_string ~start:"" ~sep:"\027[64G" ~endd:"" (
                option_to_string quoted) (
                option_to_string ~none:"" (pair_to_string BigInt.to_string BigInt.to_string))))
            (zip_with_opt a.array a.indices_array)) ::
          (option_to_string ~none:"" ~some_prefix:"Named captures:"
              (keyed_list_to_string ~nil:"\027[20G[]" ~prefix:"\027[20G# " ~key_sep:"\027[32G: " ~sep:"\n\027[20G# "
                S.to_string
                (pair_to_string ~start:"" ~sep:"\027[64G" ~endd:""
                  (option_to_string quoted)
                  (option_to_string ~none:"" (pair_to_string BigInt.to_string BigInt.to_string))))
            named_captures) ::
          []
        ))
      else
        String.concat "\n" (List.filter (fun s -> String.length s != 0) (
          ("Start: " ^ BigInt.to_string a.index) ::
          ("Captures:" ^ (
            indexed_list_to_string ~nil:"\n\tNone" ~prefix:"\n\t# " ~key_sep:" : " ~sep:"\n\t# "
              (option_to_string quoted)
            a.array)) ::
          ("Named captures:" ^ (
            option_to_string ~none:"\n\tNone" 
              (keyed_list_to_string ~nil:"\n\tNone" ~prefix:"\n\t# " ~key_sep:" : " ~sep:"\n\t# "
                S.to_string
                (option_to_string quoted))
            a.groups)) ::
          ("Indices:" ^ (
            option_to_string ~none:"\n\tNone" 
              (indexed_list_to_string ~nil:"\n\tNone" ~prefix:"\n\t# " ~key_sep:" : " ~sep:"\n\t# "
                (option_to_string ~none:"Undefined" (pair_to_string BigInt.to_string BigInt.to_string)))
            a.indices_array)) ::
          ("Named indices:" ^ (
            option_to_string ~none:"\n\tNone" 
              (keyed_list_to_string ~nil:"\n\tNone" ~prefix:"\n\t# " ~key_sep:" : " ~sep:"\n\t# "
              S.to_string
                (option_to_string ~none:"Undefined" (pair_to_string BigInt.to_string BigInt.to_string)))
            a.indices_groups)) ::
          []
        ))
  end
  open Internal

  (*  With delimited=false, the delimiters (/.../) won't be printed.
    In strict mode, the regex will be printed as is.
    In non-strict mode, an equivalent regex (through associativity) might be printed.
    Additionally, in non-strict mode, parentheses which are not required by most engines (which comform to the 'browser legacy' syntax) are not printed. *)
  let regex_to_string ?(delimited=true) ?(strict=false) (r: (P.character, P.string, P.property) coq_Regex) : ocaml_string =
    let next (i: int) : int = if strict then i + 1 else i in
    let prio_if_strict (str: ocaml_string) (at: int) (current: int) : ocaml_string = if strict then prio str at current else str in
    let rec iter (r: (P.character, P.string, P.property) coq_Regex) (current: int) : ocaml_string =
      match r with
      | Empty -> prio_if_strict "" 3 current
      | Char c -> char_lit_to_string c
      | Dot -> String.make 1 '.'
      | CharacterClass cc -> (match cc with
        | NoninvertedCC r -> "[" ^ (range_to_string r) ^ "]"
        | InvertedCC r -> "[^" ^ (range_to_string r) ^ "]")
      | AtomEsc (DecimalEsc gid) -> "\\" ^ BigInt.to_string gid
      | AtomEsc (ACharacterClassEsc esc) -> character_class_escape_to_string esc
      | AtomEsc (ACharacterEsc esc) -> character_escape_to_string esc
      | AtomEsc (GroupEsc name) -> "\\" ^ "k<" ^ S.to_string name ^ ">"
      | Disjunction (r1, r2) -> prio ((iter r1 (next 0)) ^ "|" ^ (iter r2 0)) 0 current
      | Quantified (r1, q) -> prio ((iter r1 4) ^ quantifier_to_string q) 3 current
      | Seq (r1, r2) -> prio ((iter r1 (next 1)) ^ (iter r2 1)) 1 current
      | Group (None, r1) -> "(" ^ iter r1 0 ^ ")"
      | Group (Some name, r1) -> "(?<" ^ S.to_string name ^  ">" ^ iter r1 0 ^ ")"
      | InputStart -> prio "^" 3 current
      | InputEnd -> prio_if_strict "$" 3 current
      | WordBoundary -> prio_if_strict "\\b" 3 current
      | NotWordBoundary -> prio_if_strict "\\B" 3 current
      | Lookahead (r1) -> prio_if_strict  ("(?=" ^ iter r1 0 ^ ")") 3 current
      | NegativeLookahead (r1) -> prio_if_strict  ("(?!" ^ iter r1 0 ^ ")") 3 current
      | Lookbehind (r1) -> prio_if_strict  ("(?<=" ^ iter r1 0 ^ ")") 3 current
      | NegativeLookbehind (r1) -> prio_if_strict  ("(?<!" ^ iter r1 0 ^ ")") 3 current
    in
    let res = iter r 0 in
    if delimited then "/" ^ res ^ "/" else res

  let match_state_to_string (m: (P.character) Extracted.Notation.MatchState.coq_type): ocaml_string =
    let Extracted.Notation.MatchState.{input = ls; endIndex = endIndex; captures = captures } = m in
    String.concat "\n" (List.filter (fun s -> String.length s != 0) (
          ("Input: " ^ S.to_string (P.String.list_to_string ls)) ::
          ("End: " ^ BigInt.to_string endIndex) ::
          ("Captures:" ^ (
            (indexed_list_to_string ~nil:"\n\tNone" ~prefix:"\n\t# " ~key_sep:" : " ~sep:"\n\t# "
              (option_to_string ~none:"Undefined"
                (fun p -> let Extracted.Notation.CaptureRange.{startIndex = s; endIndex = e} = p in pair_to_string BigInt.to_string BigInt.to_string (s, e))))
            captures)) ::
          []
        ))

  let match_result_to_string (r: (P.character) Extracted.Notation.coq_MatchResult): ocaml_string =
    match r with
    | None -> "No match"
    | Some m -> match_state_to_string m

  let array_exotic_to_string ?(pretty=true) (a: (P.string) Extracted.ExecArrayExotic.coq_type): ocaml_string = Internal.exec_array_exotic_to_string pretty a

  let exec_result_to_string ?(pretty=true) (r: (P.character, P.string, P.property) Extracted.execResult): ocaml_string =
    match r with
    | Null _ -> "No match"
    | Exotic (a, _) -> Internal.exec_array_exotic_to_string pretty a

  let flags_to_string (flags: Extracted.RegExpFlags.coq_type): ocaml_string =
    let s = ref "" in
    if (flags.d) then s := "d" ^ !s;
    if (flags.g) then s := "g" ^ !s;
    if (flags.i) then s := "i" ^ !s;
    if (flags.m) then s := "m" ^ !s;
    if (flags.s) then s := "s" ^ !s;
    if (flags.y) then s := "y" ^ !s;
    !s
end

