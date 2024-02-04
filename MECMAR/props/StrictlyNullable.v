From Coq Require Import PeanoNat ZArith Bool Lia List.
From Warblre Require Import Tactics Focus Result Base Patterns StaticSemantics Notation List Semantics Match EarlyErrors.

Import Result.Notations.
Import Result.Notations.Boolean.
Import Coercions.
Import Semantics.
Import MatchState.
Import Match.
Import Correctness.MatchState.

Local Open Scope result_flow.

(** * Stricly Nullable Static Analysis  *)

(* A regex is stricly nullable when if it matches, it always matches the empty string. It cannot match characters *)
(* The following function is a static under-approximation  of when is a regex striclty nullable. *)

Fixpoint strictly_nullable (r:Regex) : bool :=
  match r with
  | Empty | Lookahead _ | NegativeLookahead _ | Lookbehind _ | NegativeLookbehind _ => true
  | InputStart | InputEnd | WordBoundary | NotWordBoundary => true
  | Char _ | Dot | CharacterClass _ | AtomEsc _ => false
  | Disjunction r1 r2 | Seq r1 r2 => andb (strictly_nullable r1) (strictly_nullable r2)
  | Quantified r1 _ | Group _ r1 => strictly_nullable r1
  end.

(* For a few constructors, we could be more precise *)
(* For instance, for backreferences, we could track is the corresponding group is itself striclty nullable. *)
(* If it is, then so is the backreference *)
(* For the Quantifier, we could see as striclty nullable repetitions like {0} and {0,0} regardless of the inner regex *)

(** * Strictly Nullable Matchers  *)

Definition strictly_nullable_matcher (m:Matcher)(rer:RegExp) : Prop :=
  (* for any valid state x and continuation c and string str *)
  forall x c (VALID: Valid (input x) rer x),
    (* Then either the match fails *)
    (m x c = failure) \/
      (* or called its continuation c on some state that has he same index as x *)
      (exists y, Valid (input x) rer y /\ endIndex x = endIndex y /\ c y = m x c).


(** * Analysis Correctness  *)

Theorem strictly_nullable_analysis_correct:
  forall (r:Regex) (ctx:RegexContext) (rer:RegExp) (dir:direction) (m:Matcher)
    (STRICTLY_NULLABLE: strictly_nullable r = true)
    (COMPILE: compileSubPattern r ctx rer dir = Success m),
    strictly_nullable_matcher m rer.
Proof.
  intros r. induction r; intros ctx rer dir m STRICTLY_NULLABLE COMPILE;
    try solve[inversion STRICTLY_NULLABLE]; unfold strictly_nullable_matcher; intros x c VALID.
  - simpl in COMPILE. inversion COMPILE as [H]. clear H COMPILE.
    destruct (c x) eqn:CONT; auto.
    + destruct s; auto. right.
      exists x. split; auto.
    + right. exists x. split; auto.
  - simpl in COMPILE.
    inversion STRICTLY_NULLABLE as [SN12]. rewrite andb_true_iff in SN12. destruct SN12 as [SN1 SN2].
    clear STRICTLY_NULLABLE.
    destruct (compileSubPattern r1 (Disjunction_left r2 :: ctx) rer dir) as [m1|] eqn:SNM1; try solve[inversion COMPILE].
    apply IHr1 in SNM1; auto. clear IHr1 SN1.
    destruct (compileSubPattern r2 (Disjunction_right r1 :: ctx) rer dir) as [m2|] eqn:SNM2; try solve[inversion COMPILE].
    apply IHr2 in SNM2; auto. clear IHr2 SN2.
    inversion COMPILE as [M]. clear COMPILE M.
    (* first, excecute m1 *)
    unfold strictly_nullable_matcher in SNM1.
    specialize (SNM1 x c VALID). destruct SNM1 as [TRYRIGHT | [y [VALIDy [SAMEIDX EQUAL]]]].
    +                           (* Matcher 1 failed, try matcher 2 *)
      rewrite TRYRIGHT. simpl. apply SNM2; auto.
    +                           (* Matcher 1 succeeded *)
      rewrite <- EQUAL.
      destruct (c y) as [res|] eqn:CONT.
      * destruct res as [res|]; auto. right.
        exists y. split; auto.
      * right. exists y. split; auto.

        (* This theorem seems provable by induction this time *)
Admitted.


(** * Intermediate lemmas  *)

Lemma nil_range:
  forall x, List.Range.Nat.Bounds.range x x = nil.
Proof.
  intros x. unfold List.Range.Nat.Bounds.range, List.Range.Nat.Length.range.
  rewrite Nat.sub_diag. auto.
Qed.

Lemma update_nil:
  forall T (t:T) l,
  List.Update.Nat.Batch.update t l nil = Success l.
Proof.
  intros T t l. unfold List.Update.Nat.Batch.update. simpl. auto.
Qed.


(** * Repeating a strictly nullable matcher  *)
Lemma strictly_nullable_repeatmatcher':
  forall (r:Regex) (root:Regex) (ctx:RegexContext) (rer:RegExp) (dir:direction) (m:Matcher)
    (STRICTLY_NULLABLE: strictly_nullable r = true)
    (COMPILE: compileSubPattern r ctx rer dir = Success m)
    (RER_ADEQUACY: countLeftCapturingParensWithin root nil = RegExp.capturingGroupsCount rer)
    (ROOT: Root root r ctx)
    (EARLY_ERRORS: EarlyErrors.Pass.Regex root nil),
  forall (x:MatchState) (c:MatcherContinuation)
    (VALID: Valid (input x) rer x),
    repeatMatcher' m O%nat NoI.Inf true x c (countLeftCapturingParensBefore r ctx) (countLeftCapturingParensWithin r ctx) (repeatMatcherFuel O%nat x) = c x.
Proof.
  intros r root ctx rer dir m STRICTLY_NULLABLE COMPILE RER_ADEQUACY ROOT EARLY_ERRORS x c VALID.
  apply strictly_nullable_analysis_correct with (ctx:=ctx) (rer:=rer) (dir:=dir) (m:=m) in STRICTLY_NULLABLE; auto.
  (* we know that we have enouh fuel to do a single iteration *)
  destruct (repeatMatcherFuel 0 x) eqn:FUEL; try solve[unfold repeatMatcherFuel in FUEL; lia].
  simpl. repeat rewrite PeanoNat.Nat.add_sub.
  (* capture validity *)
  assert (CAP_VALID: Match.Correctness.Captures.Valid rer (countLeftCapturingParensBefore r ctx)
                       (countLeftCapturingParensWithin r ctx)).
  { intros i v Eq_indexed.
    pose proof (List.Indexing.Nat.success_bounds _ _ _ Eq_indexed). rewrite -> List.Range.Nat.Bounds.length in *.
    apply List.Range.Nat.Bounds.indexing in Eq_indexed.
    pose proof (EarlyErrors.countLeftCapturingParensBefore_contextualized _ _ _ ROOT EARLY_ERRORS).
    unfold countLeftCapturingParensBefore,countLeftCapturingParensWithin in *. cbn in *. lia. }
  destruct (List.Update.Nat.Batch.update None (captures x) (List.Range.Nat.Bounds.range (countLeftCapturingParensBefore r ctx) (countLeftCapturingParensBefore r ctx + countLeftCapturingParensWithin r ctx))) as [xupd|] eqn:UPD.
  (* The update for clearing internal registers cannot fail *)
  2: { apply List.Update.Nat.Batch.failure_bounds in UPD.
       unfold Match.Correctness.Captures.Valid in CAP_VALID.
       destruct VALID as [ _ [ _ [ VCL_x _ ]]]. rewrite -> VCL_x in *. contradiction. }
  (* we are valid after the update *)
  assert (UPDVALID: Valid (input x) rer (match_state (input x) (endIndex x) xupd)).
  { apply change_captures with (cap:=captures x); auto.
    - apply List.Update.Nat.Batch.success_length in UPD. rewrite <- UPD.
      destruct VALID as [_ [_ [LENGTH _]]]. auto.
    - destruct VALID as [_ [_ [_ FORALL]]].
      eapply List.Update.Nat.Batch.prop_preservation; eauto.
      apply Correctness.CaptureRange.vCrUndefined. }
  unfold strictly_nullable_matcher in STRICTLY_NULLABLE.
  specialize (STRICTLY_NULLABLE (match_state (input x) (endIndex x) xupd)
              (fun y : MatchState =>
       if (endIndex y =? endIndex x)%Z
       then None
       else
        repeatMatcher' m 0 +∞ true y c (countLeftCapturingParensBefore r ctx)
                              (countLeftCapturingParensWithin r ctx) n) UPDVALID).
  destruct STRICTLY_NULLABLE as [MISMATCH | [y [VALIDy [SAMEIDX EQUAL]]]].
  - rewrite MISMATCH. simpl. auto.
  - rewrite <- EQUAL. simpl in SAMEIDX. rewrite SAMEIDX. rewrite Z.eqb_refl. auto.
Qed.


(** * Transformation correctness: Switching a strictly nullable regex starred for a n empty is correct  *)

Theorem strictly_nullable_same_matcher:
  forall (r:Regex) (root:Regex) (ctx:RegexContext) (rer:RegExp) (dir:direction) (mstar:Matcher) (mempty:Matcher)
    (STRICTLY_NULLABLE: strictly_nullable r = true)
    (COMPILESTAR: compileSubPattern (Quantified r (Greedy Star)) ctx rer dir = Success mstar)
    (COMPILEEMPTY: compileSubPattern Empty ctx rer dir = Success mempty)
    (RER_ADEQUACY: countLeftCapturingParensWithin root nil = RegExp.capturingGroupsCount rer)
    (ROOT: Root root r (Quantified_inner (Greedy Star) :: ctx))
    (EARLY_ERRORS: EarlyErrors.Pass.Regex root nil),
  forall (x:MatchState) (c:MatcherContinuation) (VALID: Valid (input x) rer x),
    mstar x c = mempty x c.
Proof.
  intros r root ctx rer dir mstar mempty STRICTLY_NULLABLE COMPILESTAR COMPILEEMPTY RER_ADEQUACY ROOT EARLY_ERRORS x c VALID.
  simpl in COMPILEEMPTY. unfold Coercions.wrap_Matcher in COMPILEEMPTY. inversion COMPILEEMPTY. clear COMPILEEMPTY H0 mempty.
  simpl in COMPILESTAR. destruct (compileSubPattern r (Quantified_inner (Greedy Star) :: ctx) rer dir) as [m|] eqn:SUBSTAR.
  2: { inversion COMPILESTAR. }
  unfold Coercions.wrap_Matcher in COMPILESTAR. inversion COMPILESTAR as [STAR]. clear COMPILESTAR.
  apply strictly_nullable_repeatmatcher' with (x:=x) (c:=c) (root:=root) in SUBSTAR. 
  2: { apply STRICTLY_NULLABLE. }
  2: { apply RER_ADEQUACY. }
  2: { apply ROOT. }
  2: { apply EARLY_ERRORS. }
  2: { apply VALID. }
  simpl in SUBSTAR. rewrite PeanoNat.Nat.add_0_r in SUBSTAR.
  unfold repeatMatcher. rewrite SUBSTAR. auto.
Qed.                              
