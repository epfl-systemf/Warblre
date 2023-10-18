From Warblre Require Import Base.

(** 22.2.1 Patterns *)
Module Patterns.
  Definition CharSet := Character -> bool.

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