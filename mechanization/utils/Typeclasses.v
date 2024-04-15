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
End EqDec.
Notation EqDec := EqDec.type.
Infix "=?=" := EqDec.eq_dec (at level 37, no associativity).
Infix "==" := EqDec.eqb (at level 37, no associativity).
Infix "!=" := EqDec.neqb (at level 37, no associativity).

From Coq Require Import ZArith.
Instance eqdec_bool: EqDec bool := { eq_dec := Bool.bool_dec }.
Instance eqdec_nat: EqDec nat := { eq_dec := Nat.eq_dec }.
#[refine] Instance eqdec_positive: EqDec positive := {}. decide equality. Defined.
#[refine] Instance eqdec_Z: EqDec Z := {}. decide equality; apply EqDec.eq_dec. Defined.
#[refine] Instance eqdec_option {T: Type} `{EqDec T}: EqDec (option T) := {}. decide equality; apply EqDec.eq_dec. Defined.
#[refine] Instance eqdec_list {T: Type} `{EqDec T}: EqDec (list T) := {}. decide equality; apply EqDec.eq_dec. Defined.
