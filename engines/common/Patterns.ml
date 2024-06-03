include Extracted.Patterns

(* Some nifty special constructors, which are not necessarily defined in the spec. *)

(* ε, which matches the empty string (and nothing else). *)
let epsilon (type c s p): (c, s, p) coq_Regex = Empty
(* ∅, the regex which never matches anything. Encoded as /[]/. *)
let null (type c s p): (c, s, p) coq_Regex = CharacterClass (NoninvertedCC EmptyCR)

(* Unified constructor for range quantifiers. *)
let quantified (type c s p) (r: (c, s, p) coq_Regex)  (min: BigInt.t) (max: BigInt.t option) (greedy: bool): (c, s, p) coq_Regex =
  let quantifierPrefix: coq_QuantifierPrefix = match max with
    | None -> RepPartialRange (min)
    | Some max -> RepRange (min, max)
  in
  let quantifier = if greedy then Greedy quantifierPrefix else Lazy quantifierPrefix in
  Quantified (r, quantifier)