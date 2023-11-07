From Warblre Require Import Base Notation.

(** 22.2.1 Patterns *)
Module Patterns.
  Inductive QuantifierPrefix :=
  | Star
  | Plus
  | Question
  | RepExact (count: non_neg_integer)
  | RepPartialRange (min: non_neg_integer)
  | RepRange (min: non_neg_integer) (max: non_neg_integer) (OK: (min <=? max)%nat = true).

  Inductive Quantifier :=
  | Greedy (p: QuantifierPrefix)
  | Lazy (p: QuantifierPrefix).

  Inductive Regex :=
  | Empty
  | Char (A: CharSet) (invert: bool)
  | Disjunction (r1 r2: Regex)
  | Quantified (r: Regex) (q: Quantifier)
  | Seq (r1 r2: Regex)
  | Group (id: IdentifierName) (r: Regex)
  (* Assertions: ^ $ \b \B *)
  | Lookback (r: Regex)
  | Lookahead (r: Regex).

  Implicit Types (r: Regex).
End Patterns.
Export Patterns.