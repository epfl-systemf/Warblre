From Warblre Require Import Base Notation.

(** 22.2.1 Patterns *)
Module Patterns.
  Inductive Regex :=
  | Char (A: CharSet) (invert: bool)
  | Disjunction (r1 r2: Regex)
  | Kleene (r: Regex)
  | Seq (r1 r2: Regex)
  | Group (id: IdentifierName) (r: Regex)
  | Lookback (r: Regex)
  .

  Implicit Types (r: Regex).
End Patterns.
Export Patterns.