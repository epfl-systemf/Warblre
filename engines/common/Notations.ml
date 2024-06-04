open Engines
open Patterns

(* Define notations to defined regexes. *)
module CharNotations (P: EngineParameters) (S: Encoding.StringLike with type t := P.string) = struct
  let epsilon = Empty
  let group r = Group (None, r)
  let ngroup p = Group (Some (S.of_string (fst p)), (snd p))

  let (||) l r = Disjunction (l, r)

  let (!*) r = Quantified (r, Greedy Star)
  let (!*?) r = Quantified (r, Lazy Star)

  let (!+) r = Quantified (r, Greedy Plus)
  let (!+?) r = Quantified (r, Lazy Plus)

  let (!?) r = Quantified (r, Greedy Question)
  let (!??) r = Quantified (r, Lazy Question)

  let (--) r1 r2 = Seq (r1, r2)

  let (?=) r = Lookahead r
  let (?<=) r = Lookbehind r
  let (?!) r = NegativeLookahead r
  let (?<!) r = NegativeLookbehind r

  let (!$) n = assert(0 < n); AtomEsc (DecimalEsc (BigInt.of_int n))
  let (!&) n = AtomEsc (GroupEsc (S.of_string n))

  let lchar (c: P.character list): (P.character, P.string, P.property) coq_Regex =
    match c with
    | h :: [] -> Char h
    | _ -> failwith (String.cat "Invalid P.character: " (S.to_string (P.String.list_to_string c)))

  let char (c: string): (P.character, P.string, P.property) coq_Regex = lchar (P.String.list_from_string (S.of_string c))

  let ichar (c: int): (P.character, P.string, P.property) coq_Regex = Char (P.Character.from_numeric_value (BigInt.of_int c))

  let cchar (c: char): (P.character, P.string, P.property) coq_Regex = ichar (Char.code c)

  let sc c = SourceCharacter (P.Character.from_numeric_value (BigInt.of_int (Char.code c)))

  let hex_escape (h: char) (l: char) =
    let char_to_digit (c: char): Extracted.HexDigit.coq_type =
      match (Char.uppercase_ascii c) with
      | '0' -> Zero 
      | '1' -> One 
      | '2' -> Two 
      | '3' -> Three 
      | '4' -> Four 
      | '5' -> Five 
      | '6' -> Six 
      | '7' -> Seven 
      | '8' -> Eight 
      | '9' -> Nine 
      | 'A' -> A 
      | 'B' -> B 
      | 'C' -> C 
      | 'D' -> D 
      | 'E' -> E 
      | 'F' -> F 
      | _ -> failwith ("Invalid hex digit: " ^ (String.make 1 c))
    in
    HexEscape (char_to_digit h, char_to_digit l)

end

