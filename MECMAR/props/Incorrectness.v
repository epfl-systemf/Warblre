From Coq Require Import PeanoNat ZArith Bool Lia Program.Equality List.
From Warblre Require Import Tactics Specialize Focus Result Base Patterns StaticSemantics Notation Semantics Definitions Compile Correctness ClutterFree.

Import Result.Notations.
Import Semantics.
Import ClutterFree.

Parameter a: Character.
Parameter b: Character.
Axiom char_eq_refl: forall a, (a =? a = true)%Chr.
Axiom a_b_ineq: forall a, (a =? b = false)%Chr.
Axiom b_a_ineq: forall a, (b =? a = false)%Chr.

Ltac exec := repeat( cbn || rewrite -> char_eq_refl || rewrite -> a_b_ineq || rewrite -> b_a_ineq || unfold Pos.to_nat ).

Module RegexNotations.

  Declare Scope regex.
  Delimit Scope regex with regex.

  Declare Custom Entry regex.
  Notation "'</' r '/>'"  := r (r custom regex at level 99).
  Notation "r1 '|' r2" := (Disjunction r1 r2) (in custom regex at level 99, right associativity).
  Notation "r1 '~' r2" := (Seq r1 r2) (in custom regex at level 50, right associativity).
  Notation "'(' r ')'" := (Group None r) (r at level 99, in custom regex at level 1).
  Notation "'(|' n ':' r '|)'" := (Group (Some n) r) (n constr at level 0, r at level 99, in custom regex at level 1).
  Notation "'(?:' r ')'" := r (r at level 99, in custom regex at level 1).
  Notation "x" := x (in custom regex at level 0, x constr).

  Coercion Char: Character >-> Regex.

  Example example_1: </ a | a ~ a | a /> = Disjunction a (Disjunction (Seq a a) a). reflexivity. Qed.
  Example example_2: </ (?: a | a) ~ a | a /> = Disjunction (Seq (Disjunction a a) a) a. reflexivity. Qed.
  Example example_3: </ ( a ) /> = Group None a. reflexivity. Qed.

End RegexNotations.

Import RegexNotations.

Module Incorrectness.
 (*  Example disjunction_commutativity: exists (r_1 r_2: Regex) (flags: RegExp) (str: list Character) (start: non_neg_integer)
    (P00: Compile.EarlyErrorsFree.Regex </ r_1 | r_2 />)
    (P01: Compile.EarlyErrorsFree.Regex </ r_2 | r_1 />)
    (P10: Correctness.Groups.Ranges </ r_1 | r_2 /> 1 (RegExp.capturingGroupsCount flags) (RegExp.capturingGroupsCount flags))
    (P11: Correctness.Groups.Ranges </ r_2 | r_1 /> 1 (RegExp.capturingGroupsCount flags) (RegExp.capturingGroupsCount flags))
    (P2: 0 <= start <= (length str)),
    (proj1_sig (regex_match </ r_1 | r_2 /> flags str start P00 P10 P2)) <> (proj1_sig (regex_match </ r_2 | r_1 /> flags str start P01 P11 P2)).
  Proof.
    remember </ a ~ b /> as r1.
    remember </ a /> as r2.
    remember (reg_exp false false false false 0) as flags.
    remember (a :: b :: nil) as str.
    assert (P00: Compile.EarlyErrorsFree.Regex </ r1 | r2 />). {
      subst. repeat constructor.
    }
    assert (P01: Compile.EarlyErrorsFree.Regex </ r2 | r1 />). {
      subst. repeat constructor.
    }
    assert (P10: Correctness.Groups.Ranges </ r1 | r2 /> 1 (RegExp.capturingGroupsCount flags) (RegExp.capturingGroupsCount flags)). {
      admit.
    }
    assert (P11: Correctness.Groups.Ranges </ r2 | r1 /> 1 (RegExp.capturingGroupsCount flags) (RegExp.capturingGroupsCount flags)). {
      admit.
    }
    assert (P2: 0 <= 0 <= (length str)). { subst. cbn. lia. }
    exists r1. exists r2. exists flags. exists str. exists 0. exists P00. exists P01. exists P10. exists P11. exists P2.
    (* Execution gets stuck due to subset types *)
  Admitted. *)
End Incorrectness.