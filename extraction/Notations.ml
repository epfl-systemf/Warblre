open Extracted.Patterns

let epsilon = Empty
let char c =
  match Interop.string_to_utf16 c with
  | h :: [] -> Char h
  | _ -> failwith (String.cat "Invalid character: " c)
let achar c = Char (Interop.char_of_int (Char.code c))
let sc c = SourceCharacter (Interop.char_of_int (Char.code c))

let group r = Group (None, r)
let ngroup p = Group (Some (fst p), (snd p))

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

let (!$) n = assert(0 < n); AtomEsc (AtomEscape.DecimalEsc n)
let (!&) n = AtomEsc (AtomEscape.GroupEsc n)