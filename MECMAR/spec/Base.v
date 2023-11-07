From Coq Require Import ZArith Lia.
From Warblre Require Import Tactics Result.

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
Definition nat_to_nni(n: nat): non_neg_integer := n.
Coercion nat_to_nni: nat >-> non_neg_integer.
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

  Module Coercions.
    Coercion NoI.N: non_neg_integer >-> non_neg_integer_or_inf.
  End Coercions.
End NoI.
Notation "'+∞'" := NoI.Inf.
Export NoI(non_neg_integer_or_inf).

Infix "!=?" := (fun l r => negb (Nat.eqb l r)) (at level 70): nat_scope.
Infix "<=?" := Nat.leb (at level 70, no associativity): nat_scope.

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

Inductive MatchError :=
| OutOfFuel
| AssertionFailed.


(* We cheat about identifiers for now *)
Parameter IdentifierName : Type.


Module IdSet.
  Parameter t: Type.

  Parameter empty: t.
  Parameter union: t -> t -> t.
  Parameter add: IdentifierName -> t -> t.
  Parameter fold: forall {T: Type}, (IdentifierName -> T -> T) -> t -> T -> T.
End IdSet.

Module DMap.
  Parameter t: Type -> Type.

  Parameter empty: forall T, t T.
  Parameter add: forall {T: Type}, IdentifierName -> T -> t T -> t T.
  Parameter remove: forall {T: Type}, IdentifierName -> t T -> t T.
  (* Parameter removeAll: forall {T: Type}, t T -> IdSet.t -> t T. *)
End DMap.

Module Indexing.
  Local Close Scope nat.
  Local Open Scope Z.
  Local Definition get_failure {F: Type} {failure: Result.AssertionError F}: F := let (f) := failure in f.
  Local Lemma failure_helper: forall {T F: Type} {failure: Result.AssertionError F}, @Result.assertion_failed T F failure = Result.Failure get_failure.
  Proof. intros. destruct failure. reflexivity. Qed.

  Definition indexing {T F: Type} (ls: list T) (i: Z) {failure: Result.AssertionError F}: Result.Result T F := match i with
  | Z0 => Result.from_option (List.nth_error ls 0) get_failure
  | Zpos i => Result.from_option (List.nth_error ls (Pos.to_nat i)) get_failure
  | Zneg _ => Result.Failure get_failure
  end.

  Lemma failure_bounds: forall {T F: Type} {failure: Result.AssertionError F} (ls: list T) (i: Z), @indexing T F ls i failure = Result.assertion_failed <-> (i < 0 \/ (Z.of_nat (length ls)) <= i )%Z.
  Proof. intros. destruct i; delta indexing; cbn beta iota; split; intros.
    - destruct ls eqn:Eq.
      + cbn. lia.
      + rewrite -> failure_helper in *. easy.
    - destruct ls eqn:Eq.
      + rewrite -> failure_helper in *. easy.
      + subst. destruct H; [ lia | easy ].
    - destruct (List.nth_error ls (Pos.to_nat p)) eqn:Eq.
      + rewrite -> failure_helper in *. easy.
      + rewrite -> List.nth_error_None in Eq. lia.
    - destruct H; try lia.
      rewrite <- positive_nat_Z in H. rewrite <- Nat2Z.inj_le in H.
      rewrite <- List.nth_error_None in H. rewrite -> H.
      rewrite -> failure_helper in *. easy.
    - lia.
    - rewrite -> failure_helper in *. easy.
  Qed.

  Lemma failure_is_assertion: forall {T F: Type} {failure: Result.AssertionError F} (ls: list T) (i: Z) (f: F),
    indexing ls i = Result.Failure f -> f = get_failure.
  Proof.
    intros. destruct i; destruct ls; cbn in *; try injection H; try easy.
    - destruct (List.nth_error _ _) eqn:Eq in *.
      + discriminate.
      + cbn in *. congruence.
    - destruct (List.nth_error _ _) eqn:Eq in *.
      + discriminate.
      + cbn in *. congruence.
  Qed.

  Lemma failure_kind: forall {T F: Type} {failure: Result.AssertionError F} (ls: list T) (i: Z) (f: F),
    indexing ls i = Result.Failure f -> indexing ls i = Result.assertion_failed.
  Proof. intros. pose proof (failure_is_assertion ls i f H). rewrite -> failure_helper in *. congruence. Qed.
End Indexing.
Export Indexing(indexing).

Notation "ls '[' i ']'" := (indexing ls i) (at level 98, left associativity).
Notation "'set' ls '[' i ']' ':=' v 'in' z" := (let ls := DMap.add i v ls in z) (at level 200, ls at level 97, right associativity).
Notation "'set' ls '[' is '...]' ':=' v 'in' z" := (let ls := IdSet.fold (fun i => DMap.add i v) is ls in z) (at level 200, ls at level 97, right associativity).

Notation "m 'is' p" := (match m with | p => true | _ => false end) (at level 100, p pattern, no associativity).
Notation "m 'is' 'not' p" := (match m with | p => false | _ => true end) (at level 100, p pattern, no associativity).

Parameter Character: Type.