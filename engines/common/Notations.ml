(** Defines notations to define regexes
    You should either import Utf16Notations or UnicodeNotations    
*)
open Engines
open Patterns

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

  let (!$) n = assert(0 < n); AtomEsc (DecimalEsc (Host.of_int n))
  let (!&) n = AtomEsc (GroupEsc (S.of_string n))

  let lchar (c: P.character list): (P.character, P.string, P.property) coq_Regex =
    match c with
    | h :: [] -> Char h
    | _ -> failwith (String.cat "Invalid P.character: " (S.to_string (P.String.list_to_string c)))

  let char (c: string): (P.character, P.string, P.property) coq_Regex = lchar (P.String.list_from_string (S.of_string c))

  let ichar (c: int): (P.character, P.string, P.property) coq_Regex = Char (P.Character.from_numeric_value (Host.of_int c))

  let cchar (c: char): (P.character, P.string, P.property) coq_Regex = ichar (Char.code c)

  let sc c = SourceCharacter (P.Character.from_numeric_value (Host.of_int (Char.code c)))
end

