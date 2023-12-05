open Extracted.Patterns

let char c = Char (c)

let group p = Group (fst p, snd p)

let (||) l r = Disjunction (l, r)

let (!*) r = Quantified (r, Greedy Star)
let (!*?) r = Quantified (r, Lazy Star)

let (!+) r = Quantified (r, Greedy Plus)
let (!+?) r = Quantified (r, Lazy Plus)

let (!?) r = Quantified (r, Greedy Question)
let (!??) r = Quantified (r, Lazy Question)

let (--) r1 r2 = Seq (r1, r2)

let (?=) r = Lookahead r
let (?<=) r = Lookback r
let (?!) r = NegativeLookahead r
let (?<!) r = NegativeLookbehind r

let (!$) n = BackReference n