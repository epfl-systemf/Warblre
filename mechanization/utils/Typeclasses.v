From Warblre Require Import Retrieve.
From Coq Require Import ZArith Program.Equality Lia.

Local Close Scope nat.

Declare Scope wt_scope.
Delimit Scope wt_scope with wt.
Local Open Scope wt.

Module EqDec.
  Class type (T: Type) := make {
    eq_dec: forall (l r: T), {l=r} + {l<>r};
  }.

  Definition eqb {T: Type} `{type T} (l r: T): bool := if eq_dec l r then true else false.
  Definition neqb {T: Type} `{type T} (l r: T): bool := negb (eqb l r).

  Lemma inversion_true {T: Type} `{type T}: forall (l r: T), eqb l r = true <-> l = r.
  Proof. intros. unfold eqb. destruct (eq_dec l r) eqn:Eq; split; easy. Qed.

  Lemma inversion_false {T: Type} `{type T}: forall (l r: T), eqb l r = false <-> l <> r.
  Proof. intros. unfold eqb. destruct (eq_dec l r) eqn:Eq; split; easy. Qed.

  Lemma reflb {T: Type} `{type T}: forall (t: T), eqb t t = true.
  Proof. intros. unfold eqb. destruct (eq_dec t t) eqn:Eq; easy. Qed.
End EqDec.
Notation EqDec := EqDec.type.
Infix "=?=" := EqDec.eq_dec (at level 37, no associativity).
Infix "==" := EqDec.eqb (at level 37, no associativity).
Infix "!=" := EqDec.neqb (at level 37, no associativity).
Infix "==#" := EqDec.eq_dec (at level 70, no associativity): wt_scope.
Infix "==?" := EqDec.eqb (at level 70, no associativity): wt_scope.
Infix "!=?" := EqDec.neqb (at level 70, no associativity): wt_scope.

Instance eqdec_bool: EqDec bool := { eq_dec := Bool.bool_dec }.
Instance eqdec_nat: EqDec nat := { eq_dec := Nat.eq_dec }.
#[refine] Instance eqdec_positive: EqDec positive := {}. decide equality. Defined.
#[refine] Instance eqdec_Z: EqDec Z := {}. decide equality; apply EqDec.eq_dec. Defined.
(* The cost (10) is a band-aid fix to avoid stack overflows when resolving EqDec in some theorems (e.g. EarlyErrors.groupSpecifiersThatMatch_singleton). TODO: investigate *)
#[refine] Instance eqdec_option {T: Type} `{EqDec T}: EqDec (option T) | 10 := {}. decide equality; apply EqDec.eq_dec. Defined.
#[refine] Instance eqdec_list {T: Type} `{EqDec T}: EqDec (list T) | 10 := {}. decide equality; apply EqDec.eq_dec. Defined.
