open Extracted.Patterns

let char c = Char ((fun d -> d == c), false)

let group p = Group (fst p, snd p)

let (||) l r = Disjunction (l, r)

let (!*) r = Quantified (r, Greedy Star)
let (!*?) r = Quantified (r, Lazy Star)

let (!+) r = Quantified (r, Greedy Plus)
let (!+?) r = Quantified (r, Lazy Plus)

let (!?) r = Quantified (r, Greedy Question)
let (!??) r = Quantified (r, Lazy Question)

let (--) r1 r2 = Seq (r1, r2)

let (?<=) r = Lookback r
let (?=) r = Lookahead r