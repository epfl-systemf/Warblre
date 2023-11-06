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
Definition non_neg_integer_or_inf := option nat.

Infix "=?" := Z.eqb (at level 70): Z_scope.
Infix "<?" := Z.ltb (at level 70): Z_scope.
Infix "<=?" := Z.leb (at level 70): Z_scope.
Infix ">?" := Z.gtb (at level 70): Z_scope.
Infix ">=?" := Z.geb (at level 70): Z_scope.

Inductive MatchError :=
| OutOfFuel
| AssertionFailed.


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

Notation "'+∞'" := (@None nat).

Notation "m 'is' p" := (match m with | p => true | _ => false end) (at level 100, p pattern, no associativity).
Notation "m 'is' 'not' p" := (match m with | p => false | _ => true end) (at level 100, p pattern, no associativity).

(* Notation "x '<=' y" := (Z.compare x y = Lt \/ Z.compare x y = Eq). *)

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

Parameter Character: Type.