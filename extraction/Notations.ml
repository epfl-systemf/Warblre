(** Defines notations to define regexes
    You should either import Utf16Notations or UnicodeNotations    
*)
open Extracted.Patterns

module CharNotations (S: Encoding.Character) = struct
  type character = S.character

  let epsilon = Empty
  let group r = Group (None, r)
  let ngroup p = Group (Some (Encoding.Utf16.list_from_string (fst p)), (snd p))

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
  let (!&) n = AtomEsc (GroupEsc (Encoding.Utf16.list_from_string n))

  let lchar (c: character list): character coq_Regex =
    match c with
    | h :: [] -> Char h
    | _ -> failwith (String.cat "Invalid character: " (S.list_to_string c))

  let char (c: string): character coq_Regex = lchar (S.list_from_string c)

  let ichar (c: int): character coq_Regex = lchar (S.chars_from_int c)

  let cchar (c: char): character coq_Regex = ichar (Char.code c)

  let sc c = SourceCharacter (S.char_from_int (Char.code c))
end

module Utf16Notations = CharNotations(Encoding.Utf16)
module UnicodeNotations = struct
  module Base = CharNotations(Encoding.Unicode)
  include Base

  let uprop n = AtomEsc (ACharacterClassEsc (UnicodeProp (Obj.magic (Interop.UnicodeProperties.Predicate n))))
end