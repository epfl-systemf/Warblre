(** Defines notations to define regexes
    You should either import Utf16Notations or UnicodeNotations    
*)
open Engines
open Patterns

module CharNotations (P: EngineParameters) = struct
  type character = P.character

  let list_from_string s = Obj.magic (P.String.list_from_string (P.String.from_host s))
  let list_to_string s = P.String.to_host (P.String.list_to_string s)

  let epsilon = Empty
  let group r = Group (None, r)
  let ngroup p = Group (Some (list_from_string (fst p)), (snd p))

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

  let (!$) n = assert(0 < n); AtomEsc (DecimalEsc n)
  let (!&) n = AtomEsc (GroupEsc (list_from_string n))

  let lchar (c: character list): (character, P.string) coq_Regex =
    match c with
    | h :: [] -> Char h
    | _ -> failwith (String.cat "Invalid character: " (list_to_string c))

  let char (c: string): (character, P.string) coq_Regex = lchar (list_from_string c)

  let ichar (c: int): (character, P.string) coq_Regex = Char (P.Character.from_numeric_value c)

  let cchar (c: char): (character, P.string) coq_Regex = ichar (Char.code c)

  let sc c = SourceCharacter (P.Character.from_numeric_value (Char.code c))
end

module Utf16Notations = CharNotations(Utf16Parameters)
module UnicodeNotations = struct
  module Base = CharNotations(UnicodeParameters)
  include Base

  let uprop n = AtomEsc (ACharacterClassEsc (UnicodeProp (Obj.magic (Engines.UnicodeProperty.Predicate n))))
end