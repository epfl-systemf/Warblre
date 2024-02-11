From Coq Require Import ZArith Lia.
From Warblre Require Import Result.

Import Result.Notations.
Local Open Scope result_flow.

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
Definition positive_integer := positive.
Definition nat_to_nni (n: nat): non_neg_integer := n.
Definition positive_to_non_neg (n: positive_integer): non_neg_integer := Pos.to_nat n.
Definition positive_to_nat (n: positive_integer): nat := Pos.to_nat n.

Module NonNegInt.
  Definition modulo (i: non_neg_integer) (modulus: non_neg_integer): non_neg_integer := Nat.modulo i modulus.
  #[global] Opaque modulo.

  Lemma pos: forall p, positive_to_non_neg p > 0.
  Proof. intros. pose proof (Pos2Nat.is_pos p). unfold positive_to_non_neg. lia. Qed.

  Fixpoint to_positive {F: Type} {_: Result.AssertionError F} (n: non_neg_integer): Result positive_integer F :=
     match n with
       | 0 => Result.assertion_failed
       | 1 => Success (1%positive)
       | S x => let! n' =<< to_positive x in Success (Pos.succ n')
     end.

  Lemma succ {F: Type} {_: Result.AssertionError F}: forall n p, to_positive n = Success p -> to_positive (S n) = Success (Pos.succ p).
  Proof. intros. cbn in *. destruct n. - Result.assertion_failed_helper. - rewrite -> H. reflexivity. Qed.

  Lemma succ_inv {F: Type} {_: Result.AssertionError F}: forall n p, to_positive (S (S n)) = Success (Pos.succ p) -> to_positive (S n) = Success p.
  Proof. intros. cbn in *. match goal with | [ |- ?t = _ ] => destruct t end. - injection H as ->%Pos.succ_inj. reflexivity. - discriminate. Qed.

  Lemma to_positive_soundness {F: Type} {_: Result.AssertionError F}: forall n p, to_positive n = Success p -> positive_to_non_neg p = n.
  Proof.
    induction n; intros; cbn in *.
    - Result.assertion_failed_helper. 
    - destruct n.
      + injection H as <-. reflexivity.
      + destruct (to_positive (S n)).
        * injection H as <-. subst. specialize IHn with (1 := eq_refl).
          unfold positive_to_non_neg. rewrite -> Pos2Nat.inj_succ. f_equal. assumption.
        * discriminate.
  Qed.

  Lemma to_positive_completeness {F: Type} {_: Result.AssertionError F}: forall n, 0 < n -> exists p, to_positive n = Success p.
  Proof.
    induction n; intros.
    - lia.
    - destruct n.
      + exists 1%positive. reflexivity.
      + specialize (IHn ltac:(lia)) as [ p Eq_p ]. exists (Pos.succ p). apply succ. assumption.
  Qed.

  Lemma failure {F: Type} {_: Result.AssertionError F}: forall n f, to_positive n = Failure f -> n = 0.
  Proof. intros. destruct n eqn:Eq_n. - reflexivity. - pose proof (to_positive_completeness (S n0) ltac:(lia)) as [ ? ? ]. congruence. Qed.
End NonNegInt.

Module NNI.
  Lemma sub_lower: forall i j n, (n <= i)%nat -> (n <= j)%nat -> (i - n = j - n)%nat -> (i = j)%nat.
  Proof. intros. lia. Qed.
End NNI.

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
Infix ">?" := (fun l r => (l >=? S r)%nat) (at level 70, no associativity): nat_scope.

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