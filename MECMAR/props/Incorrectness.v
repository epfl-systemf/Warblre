From Coq Require Import PeanoNat ZArith Bool Lia Program.Equality List.
From Warblre Require Import Tactics Specialize Focus Result Base Patterns StaticSemantics Notation Semantics Definitions.

Import Result.Notations.
Import Semantics.

Parameter a: Character.
Axiom char_eq_refl: forall a, (a =? a = true)%Chr.

Module RegexNotations.

  Declare Scope regex.
  Delimit Scope regex with regex.

  Declare Custom Entry regex.
  Notation "'</' r '/>'"  := r (r custom regex at level 99).
  Notation "r1 '|' r2" := (Disjunction r1 r2) (in custom regex at level 99, right associativity).
  Notation "r1 '~' r2" := (Seq r1 r2) (in custom regex at level 50, right associativity).
  Notation "'(|' n ':' r '|)'" := (Group n r) (n constr at level 0, r at level 99, in custom regex at level 1).
  Notation "'(' r ')'" := r (r at level 99, in custom regex at level 1).
  Notation "x" := x (in custom regex at level 0, x constr).

  Coercion Char: Character >-> Regex.

  Example example_1: </ a | a ~ a | a /> = Disjunction a (Disjunction (Seq a a) a). reflexivity. Qed.
  Example example_2: </ (a | a) ~ a | a /> = Disjunction (Seq (Disjunction a a) a) a. reflexivity. Qed.
  Example example_3: </ (|3: a |) /> = Group 3 a. reflexivity. Qed.

End RegexNotations.

Import RegexNotations.

Module Incorrectness.
  Example disjunction_commutativity: exists (r_1 r_2: Regex) (flags: RegExp) (str: list Character) (start: non_neg_integer),
    compilePattern </ r_1 | r_2 /> flags str start <> compilePattern </ r_2 | r_1 /> flags str start.
  Proof.
    exists </ (|0: a |) />. exists </ (|1: a |) />.
    exists (reg_exp 2).
    exists (a :: nil). exists 0.
    repeat( cbn || rewrite -> char_eq_refl || unfold Pos.to_nat ).
    easy.
  Qed.
End Incorrectness.