include Extracted.Patterns

let epsilon (type c s p): (c, s, p) coq_Regex = Empty
let null (type c s p): (c, s, p) coq_Regex = CharacterClass (InvertedCC EmptyCR)

(* 'Smart' constructors for regexes *)
module Smart = struct 
  let disjunction (type c s p) (l: (c, s, p) coq_Regex) (r: (c, s, p) coq_Regex): (c, s, p) coq_Regex =
    match l, r with
    | CharacterClass (InvertedCC EmptyCR), r -> r
    | l, CharacterClass (InvertedCC EmptyCR) -> l
    | l, r -> Disjunction (l, r)

  let seq (type c s p) (l: (c, s, p) coq_Regex) (r: (c, s, p) coq_Regex): (c, s, p) coq_Regex =
    match l, r with
    | Empty, r -> r
    | l, Empty -> l
    | l, r -> Seq (l, r)

  let quantified (type c s p) (r: (c, s, p) coq_Regex)  (min: Host.integer) (max: Host.integer option) (greedy: bool): (c, s, p) coq_Regex =
    let quantifierPrefix: coq_QuantifierPrefix = match max with
      | None -> RepPartialRange (min)
      | Some max -> RepRange (min, max)
    in
    let quantifier = if greedy then Greedy quantifierPrefix else Lazy quantifierPrefix in
    Quantified (r, quantifier)
end