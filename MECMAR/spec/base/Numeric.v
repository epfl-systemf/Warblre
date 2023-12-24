From Coq Require Import ZArith Lia.
From Warblre Require Import Result.

(* 5.2.5 Mathematical Operations
   «  Mathematical values: Arbitrary real numbers, used as the default numeric type. »
   «  When the term integer is used in this specification, it refers to a mathematical 
      value which is in the set of integers, unless otherwise stated. When the term integral 
      Number is used in this specification, it refers to a Number value whose mathematical
      value is in the set of integers. »
   ... so, that should be a Real? (note that "integers" redirects to the second definition).
*)
Definition integer := Z.
Definition non_neg_integer := nat.
Definition positive_integer := { n: non_neg_integer | (0 < n)%nat }.
Definition nat_to_nni (n: nat): non_neg_integer := n.
Definition positive_to_non_neg (n: positive_integer): non_neg_integer := proj1_sig n.
Definition positive_to_nat (n: positive_integer): nat := proj1_sig n.

Module NonNegInt.
  Definition to_positive {F: Type} {_: Result.AssertionError F} (n: non_neg_integer): Result positive_integer F.
    destruct n eqn:Eq_n.
    - apply Result.assertion_failed.
    - refine (Success (exist _ n _)). subst. apply Nat.lt_0_succ.
  Defined.

  Lemma to_positive_soundness {F: Type} {_: Result.AssertionError F}: forall n p, to_positive n = Success p -> proj1_sig p = n.
  Proof. intros. destruct n; cbn in *. - Result.assertion_failed_helper. - injection H as <-. reflexivity. Qed.

  Lemma to_positive_completeness {F: Type} {_: Result.AssertionError F}: forall n, 0 < n -> exists p, to_positive n = Success p.
  Proof. intros. destruct n. - lia. - cbn. eexists. reflexivity. Qed.
End NonNegInt.


(* Nat or Infinity *)
Module NoI.
  Inductive non_neg_integer_or_inf :=
  | N (n: non_neg_integer)
  | Inf.

  Definition eqb (l r: non_neg_integer_or_inf): bool := match l, r with
  | N l', N r' => Nat.eqb l' r'
  | Inf, Inf => true
  | _, _ => false
  end.

  Definition add (l r: non_neg_integer_or_inf): non_neg_integer_or_inf := match l, r with
  | N l', N r' => N (Nat.add l' r')
  | _, _ => Inf
  end.

  Definition sub (l: non_neg_integer_or_inf) (r: non_neg_integer): non_neg_integer_or_inf := match l with
  | N l' => N (Nat.sub l' r)
  | _=> Inf
  end.

  Definition leqb (l: non_neg_integer) (r: non_neg_integer_or_inf): bool := match r with
  | N r' => (l <=? r')%nat
  | Inf => true
  end.
End NoI.
Notation "'+∞'" := NoI.Inf.
Export NoI(non_neg_integer_or_inf).

Infix "!=?" := (fun l r => negb (Nat.eqb l r)) (at level 70): nat_scope.
Infix "<=?" := Nat.leb (at level 70, no associativity): nat_scope.
Infix ">=?" := (fun l r => Nat.leb r l) (at level 70, no associativity): nat_scope.

Declare Scope NoI_scope.
Delimit Scope NoI_scope with NoI.
Infix "=?" := NoI.eqb (at level 70): NoI_scope.
Infix "+" := NoI.add (at level 50, left associativity): NoI_scope.
Infix "-" := NoI.sub (at level 50, left associativity): NoI_scope.
Infix "<=?" := NoI.leqb (at level 70, no associativity): NoI_scope.

Infix "=?" := Z.eqb (at level 70): Z_scope.
Infix "!=?" := (fun l r => negb (Z.eqb l r)) (at level 70): Z_scope.
Infix "<?" := Z.ltb (at level 70): Z_scope.
Infix "<=?" := Z.leb (at level 70): Z_scope.
Infix ">?" := Z.gtb (at level 70): Z_scope.
Infix ">=?" := Z.geb (at level 70): Z_scope.