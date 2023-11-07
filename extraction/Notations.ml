open Extracted.Patterns

let char c = Char ((fun d -> d == c), false)

let (||) l r = Disjunction (l, r)

let (!*) r = Quantified (r, Greedy Star)

let (--) r1 r2 = Seq (r1, r2)

let group p = Group (fst p, snd p)

let (!<=) r = Lookback r