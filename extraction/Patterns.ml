include Extracted.Patterns

let epsilon (type c s): (c, s) coq_Regex = Empty
let null (type c s): (c, s) coq_Regex = CharacterClass (InvertedCC EmptyCR)

(* 'Smart' constructors for regexes *)
module Smart = struct 
  let disjunction (type c s) (l: (c, s) coq_Regex) (r: (c, s) coq_Regex): (c, s) coq_Regex =
    match l, r with
    | CharacterClass (InvertedCC EmptyCR), r -> r
    | l, CharacterClass (InvertedCC EmptyCR) -> l
    | l, r -> Disjunction (l, r)

  let seq (type c s) (l: (c, s) coq_Regex) (r: (c, s) coq_Regex): (c, s) coq_Regex =
    match l, r with
    | Empty, r -> r
    | l, Empty -> l
    | l, r -> Seq (l, r)

  let quantified (type c s) (r: (c, s) coq_Regex)  (min: int) (max: int option) (greedy: bool): (c, s) coq_Regex =
    let quantifierPrefix: coq_QuantifierPrefix = match max with
      | None -> RepPartialRange (min)
      | Some max -> RepRange (min, max)
    in
    let quantifier = if greedy then Greedy quantifierPrefix else Lazy quantifierPrefix in
    Quantified (r, quantifier)
end