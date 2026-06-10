From Stdlib Require Import PeanoNat ZArith Bool Lia List.
From Warblre Require Import Tactics Focus Result Base Errors Patterns Node StaticSemantics Notation List Semantics Match EarlyErrors RegExpRecord.

Import Notation.
Import Patterns.
Import Result.Notations.
Import Result.Notations.Boolean.
Import Coercions.
Import Semantics.
Import Notation.MatchState.
Import Match.
Import Match.MatchState.
Import Match.

Local Open Scope result_flow.

(** * Stricly Nullable Static Analysis  *)
Section StriclyNullable.
  Context `{specParameters: Parameters}.
(* A regex is stricly nullable when if it matches, it always matches the empty string. It cannot match characters *)
(* The following function is a static under-approximation  of when is a regex striclty nullable. *)

Fixpoint strictly_nullable (r:Regex) : bool :=
  match r with
  | Empty | Lookahead _ | NegativeLookahead _ | Lookbehind _ | NegativeLookbehind _ => true
  | InputStart | InputEnd | WordBoundary | NotWordBoundary => true
  | Char _ | Dot | CharacterClass _ | AtomEsc _ => false
  | Disjunction r1 r2 | Seq r1 r2 => andb (strictly_nullable r1) (strictly_nullable r2)
  | Quantified r1 _ | Group _ r1 | ModifyGroupAdd _ r1 | ModifyGroupAddRemove _ _ r1 => strictly_nullable r1
  end.

(* For a few constructors, we could be more precise *)
(* For instance, for backreferences, we could track is the corresponding group is itself striclty nullable. *)
(* If it is, then so is the backreference *)
(* For the Quantifier, we could see as striclty nullable repetitions like {0} and {0,0} regardless of the inner regex *)

(** * Strictly Nullable Matchers  *)

Definition strictly_nullable_matcher (m:Matcher) (rer:RegExpRecord) : Prop :=
  (* for any valid state x and continuation c and string str *)
  forall x c (VALID: Valid (input x) rer x),
    (* Then either the match fails *)
    (m x c = failure) \/
      (* or called its continuation c on some state that has the same index as x *)
      (exists y, Valid (input x) rer y /\ endIndex x = endIndex y /\ c y = m x c).


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

Lemma list_filter_success:
  forall {T F:Type} (l:list T) (f:T -> Result bool F)
    (SUCCESSF: forall t, exists res, f t = Success res),
  exists res, List.Filter.filter l f = Success res.
Proof.
  intros T F l f SUCCESSF. induction l; simpl; eauto.
  specialize (SUCCESSF a) as [fres FEQ]. rewrite FEQ.
  simpl. destruct IHl as [res FILTER]. rewrite FILTER. simpl.
  destruct fres; eauto.
Qed.

Lemma isWordsuccess :
  forall x rer (VALID: Valid (input x) rer x),
  exists res, isWordChar rer (input x) (endIndex x) = Success res.
Proof.
  intros x rer VALID. unfold isWordChar.
  destruct VALID as [_ [ITER _]]. unfold IteratorOn in ITER.
  destruct (endIndex x =? -1)%Z eqn:POS; try lia. simpl.
  destruct (endIndex x =? length (input x))%Z eqn:END; eauto.
  assert (NOFAILURE: (0 <= endIndex x < length (input x))%Z) by lia.
  destruct (List.Indexing.Int.indexing (input x) (endIndex x)) eqn:INDEX.    
  2: { rewrite <- List.Indexing.Int.success_bounds0 in NOFAILURE. rewrite INDEX in NOFAILURE. destruct NOFAILURE. inversion H. }
  cbn.
  unfold wordCharacters.
  unfold CharSet.filter.
  match goal with | [ |- context[if ?b then _ else _]] => destruct (b); eauto end.
Qed.

Lemma isWordsuccess_minusone :
  forall x rer (VALID: Valid (input x) rer x),
  exists res, isWordChar rer (input x) (endIndex x - 1)%Z = Success res.
Proof.
  intros x rer VALID. unfold isWordChar.
  destruct VALID as [_ [ITER _]]. unfold IteratorOn in ITER.
  destruct (endIndex x - 1 =? -1)%Z eqn:POS; simpl; eauto.
  destruct (endIndex x - 1 =? length (input x))%Z eqn:END; simpl; eauto.
  assert (NOFAILURE: (0 <= endIndex x - 1 < length (input x))%Z) by lia.
  destruct (List.Indexing.Int.indexing (input x) (endIndex x - 1)) eqn:INDEX.    
  2: { rewrite <- List.Indexing.Int.success_bounds0 in NOFAILURE. rewrite INDEX in NOFAILURE. destruct NOFAILURE. inversion H. }
  destruct (wordCharacters rer) eqn:WORD.
  - cbn. match goal with [ |- context[if ?b then _ else _]] => destruct b; eauto end.
  - exfalso. eapply Compile.wordCharacters. eauto.
Qed.

Lemma valid_trans:
  forall (x y:MatchState) (rer:RegExpRecord)
    (VALIDx: Valid (input x) rer x)
    (VALIDy: Valid (input x) rer y),
    Valid (input x) rer (match_state (input x) (endIndex x) (captures y)).
Proof.
  intros x y rer VALIDx VALIDy.
  destruct VALIDx as [ONx [ITERx [LENx FORALLx]]]. destruct VALIDy as [ONy [ITERy [LENy FORALLy]]].
  unfold Valid. split; auto.
Qed.

Lemma valid_input:
  forall (x y:MatchState) (rer:RegExpRecord)
    (VALIDy: Valid (input x) rer y),
    Valid (input y) rer y.
Proof.
  intros x y rer VALIDy. destruct VALIDy as [ONy [ITERy [LENy FORALLy]]].
  unfold OnInput in ONy. rewrite ONy. split; auto.
Qed.

(* Capture Reset lemmas *)
Lemma capture_reset_validity:
  forall (r:Regex) (root:Regex) (ctx:RegexContext) (rer:RegExpRecord)
    (RER_ADEQUACY: countLeftCapturingParensWithin root nil = RegExpRecord.capturingGroupsCount rer)
    (ROOT: Root root (r, ctx))
    (EARLY_ERRORS: EarlyErrors.Pass_Regex root nil),
    Captures.Valid rer (countLeftCapturingParensBefore r ctx) (countLeftCapturingParensWithin r ctx).
Proof.
  intros r root ctx rer RER_ADEQUACY ROOT EARLY_ERRORS.
  intros i v Eq_indexed.
  pose proof (List.Indexing.Nat.success_bounds _ _ _ Eq_indexed). rewrite -> List.Range.Nat.Bounds.length in *.
  apply List.Range.Nat.Bounds.indexing in Eq_indexed.
  pose proof (EarlyErrors.countLeftCapturingParensBefore_contextualized _ _ _ ROOT EARLY_ERRORS).
  unfold countLeftCapturingParensBefore,countLeftCapturingParensWithin in *. lia.
Qed.

Lemma capture_reset_success:
  forall (r:Regex) (ctx:RegexContext) (rer:RegExpRecord)
    (x:MatchState) (VALID: Valid (input x) rer x)
    (CAP_VALID: Captures.Valid rer (countLeftCapturingParensBefore r ctx) (countLeftCapturingParensWithin r ctx)),
  exists capupd, List.Update.Nat.Batch.update None (captures x) (List.Range.Nat.Bounds.range (countLeftCapturingParensBefore r ctx) (countLeftCapturingParensBefore r ctx + countLeftCapturingParensWithin r ctx)) = Success capupd.
Proof.
  intros r ctx rer x VALID CAP_VALID.
  destruct (List.Update.Nat.Batch.update None (captures x) (List.Range.Nat.Bounds.range (countLeftCapturingParensBefore r ctx) (countLeftCapturingParensBefore r ctx + countLeftCapturingParensWithin r ctx))) as [xupd|] eqn:UPD; eauto.
  apply List.Update.Nat.Batch.failure_bounds in UPD.
  unfold Captures.Valid in CAP_VALID.
  destruct VALID as [ _ [ _ [ VCL_x _ ]]]. rewrite -> VCL_x in *. contradiction. 
Qed.

Lemma quant_capture_reset_success:
  forall (r:Regex) (ctx:RegexContext) (rer:RegExpRecord) (q:Quantifier)
    (x:MatchState) (VALID: Valid (input x) rer x)
    (CAP_VALID: Captures.Valid rer (countLeftCapturingParensBefore r ctx) (countLeftCapturingParensWithin r ctx)),
  exists capupd, List.Update.Nat.Batch.update None (captures x) (List.Range.Nat.Bounds.range (countLeftCapturingParensBefore r ctx) (countLeftCapturingParensBefore r ctx + countLeftCapturingParensWithin r (Quantified_inner q::ctx))) = Success capupd.
Proof.
  intros r ctx rer q x VALID CAP_VALID.
  destruct (List.Update.Nat.Batch.update None (captures x) (List.Range.Nat.Bounds.range (countLeftCapturingParensBefore r ctx) (countLeftCapturingParensBefore r ctx + countLeftCapturingParensWithin r ctx))) as [xupd|] eqn:UPD; eauto.
  apply List.Update.Nat.Batch.failure_bounds in UPD.
  unfold Captures.Valid in CAP_VALID.
  destruct VALID as [ _ [ _ [ VCL_x _ ]]]. rewrite -> VCL_x in *. contradiction. 
Qed.


Lemma capture_reset_preserve_validity:
  forall (r:Regex) (ctx:RegexContext) (rer:RegExpRecord)
    (x:MatchState) (VALID: Valid (input x) rer x)
    (xupd: list (option CaptureRange))
    (UPD: List.Update.Nat.Batch.update None (captures x) (List.Range.Nat.Bounds.range (countLeftCapturingParensBefore r ctx) (countLeftCapturingParensBefore r ctx + countLeftCapturingParensWithin r ctx)) = Success xupd),
    Valid (input x) rer (match_state (input x) (endIndex x) xupd).
Proof.
  intros r ctx rer x VALID xupd UPD. 
  apply change_captures with (cap:=captures x); auto.
    - apply List.Update.Nat.Batch.success_length in UPD. rewrite <- UPD.
      destruct VALID as [_ [_ [LENGTH _]]]. auto.
    - destruct VALID as [_ [_ [_ FORALL]]].
      eapply List.Update.Nat.Batch.prop_preservation; eauto.
      apply Match.CaptureRange.vCrUndefined.
Qed.

Lemma quant_capture_reset_preserve_validity:
  forall (r:Regex) (ctx:RegexContext) (rer:RegExpRecord) (q:Quantifier)
    (x:MatchState) (VALID: Valid (input x) rer x)
    (xupd: list (option CaptureRange))
    (UPD: List.Update.Nat.Batch.update None (captures x) (List.Range.Nat.Bounds.range (countLeftCapturingParensBefore r ctx) (countLeftCapturingParensBefore r ctx + countLeftCapturingParensWithin r (Quantified_inner q::ctx))) = Success xupd),
    Valid (input x) rer (match_state (input x) (endIndex x) xupd).
Proof.
  intros r ctx rer q x VALID xupd UPD. 
  apply change_captures with (cap:=captures x); auto.
    - apply List.Update.Nat.Batch.success_length in UPD. rewrite <- UPD.
      destruct VALID as [_ [_ [LENGTH _]]]. auto.
    - destruct VALID as [_ [_ [_ FORALL]]].
      eapply List.Update.Nat.Batch.prop_preservation; eauto.
      apply Match.CaptureRange.vCrUndefined.
Qed.

    

(** * Analysis Correctness  *)

(* analysis correctness lemmas for the repeat matcher *)
(* when min=0, we directly get the termination of repeatmatcher since we are repeating a strictly nullable matcher *)
Lemma repeat_matcher_min_0:
  forall (r:Regex) (root:Regex) (s:Matcher) (q:Quantifier) (rer:RegExpRecord) (ctx:RegexContext)
    (x:MatchState) (c:MatcherContinuation) (max:non_neg_integer_or_inf) (fuel:nat)
    (VALID: Valid (input x) rer x)
    (RER_ADEQUACY: countLeftCapturingParensWithin root nil = RegExpRecord.capturingGroupsCount rer)
    (ROOT: Root root (Quantified r q, ctx))
    (EARLY_ERRORS: EarlyErrors.Pass_Regex root nil)
    (SN: strictly_nullable_matcher s rer),
    repeatMatcher' s 0 max
      (CompiledQuantifier_greedy (compileQuantifier q)) x c (countLeftCapturingParensBefore r ctx)
      (countLeftCapturingParensWithin r (Quantified_inner q :: ctx)) (S fuel) = None \/
      (exists y : MatchState,
          Valid (input x) rer y /\
            endIndex x = endIndex y /\
            c y =
              repeatMatcher' s 0 max
                (CompiledQuantifier_greedy (compileQuantifier q)) x c (countLeftCapturingParensBefore r ctx)
                (countLeftCapturingParensWithin r (Quantified_inner q :: ctx)) (S fuel)).
Proof.
  intros r root s q rer ctx x c max fuel VALID RER_ADEQUACY ROOT EARLY_ERRORS SN.
  (* capture reset succeeds and preserves validity *)
  pose proof (capture_reset_validity (Quantified r q) root ctx rer RER_ADEQUACY ROOT EARLY_ERRORS) as CAP_VALID.
  pose proof (quant_capture_reset_success r ctx rer q x VALID CAP_VALID) as [xupd UPD]. 
  pose proof (quant_capture_reset_preserve_validity r ctx rer q x VALID xupd UPD) as UPDVALID.
  destruct q as [q|q]; simpl.
    (* greedy *)
  - 
    destruct (max =? 0)%NoI eqn:MAX.
    (* max = 0 *)
    { right. exists x. split; auto. }
    repeat rewrite PeanoNat.Nat.add_sub.
    rewrite UPD. simpl.
    match goal with
    | [ H:_ |- context[s ?x ?c]] => specialize (SN x c UPDVALID)
    end.
    destruct SN as [NONE | [y [VALIDy [END EQUAL]]]].
    * rewrite NONE. simpl. right. exists x. split; auto.
    * rewrite <- EQUAL. simpl in END. rewrite END. rewrite Z.eqb_refl. simpl.
      right. exists x. split; auto.
  -                           (* lazy *)
    destruct (max =? 0)%NoI eqn:MAX.
    (* max = 0 *)
    { right. exists x. split; auto. }
    repeat rewrite PeanoNat.Nat.add_sub.
    rewrite UPD. simpl.
    destruct (c x) as [[succeed|]|f] eqn:CONT;
      try solve[right; exists x; split; auto].
    (* skipping the quantifier failed and we backtrack *)
    simpl.
    match goal with
    | [ H:_ |- context[s ?x ?c]] => specialize (SN x c UPDVALID)
    end.
    destruct SN as [NONE | [y [VALIDy [END EQUAL]]]].
    * rewrite NONE. auto.
    * rewrite <- EQUAL. simpl in END. rewrite END. rewrite Z.eqb_refl. auto.
Qed.


(* when min>0, we can proceed by induction on min until we reach min=0, the previous case *)
(* during all the mandatroy repetitions, we keep being valid and at the same index in the string *)
Lemma repeat_matcher_sn:
  forall (r:Regex) (root:Regex) (s:Matcher) (q:Quantifier) (rer:RegExpRecord) (ctx:RegexContext)
    (min:nat) (max:non_neg_integer_or_inf) (fuel:nat)
    (x:MatchState) (c:MatcherContinuation)
    (VALID: Valid (input x) rer x)
    (RER_ADEQUACY: countLeftCapturingParensWithin root nil = RegExpRecord.capturingGroupsCount rer)
    (ROOT: Root root (Quantified r q, ctx))
    (EARLY_ERRORS: EarlyErrors.Pass_Regex root nil)
    (FUEL: fuel > min)
    (SN: strictly_nullable_matcher s rer),
    repeatMatcher' s min max
      (CompiledQuantifier_greedy (compileQuantifier q)) x c (countLeftCapturingParensBefore r ctx)
      (countLeftCapturingParensWithin r (Quantified_inner q :: ctx)) fuel = None \/
      (exists y : MatchState,
          Valid (input x) rer y /\
            endIndex x = endIndex y /\
            c y =
              repeatMatcher' s min max
                (CompiledQuantifier_greedy (compileQuantifier q)) x c (countLeftCapturingParensBefore r ctx)
                (countLeftCapturingParensWithin r (Quantified_inner q :: ctx)) fuel).
Proof.
  intros r root s q rer ctx min. 
  induction min; intros.
  - destruct fuel; try solve[lia].
    apply repeat_matcher_min_0 with (root:=root); auto.
  - destruct fuel; try solve[lia]. (* enough fuel for an iteration *)
    simpl. destruct (max =? 0)%NoI eqn:MAX.
    (* for max = 0, directly calls the continuation *)
    { right. exists x. split; auto. }
    repeat rewrite PeanoNat.Nat.add_sub.
    (* capture reset succeeds and preserves validity *)
    pose proof (capture_reset_validity (Quantified r q) root ctx rer RER_ADEQUACY ROOT EARLY_ERRORS) as CAP_VALID.
    pose proof (quant_capture_reset_success r ctx rer q x VALID CAP_VALID) as [xupd UPD]. 
    pose proof (quant_capture_reset_preserve_validity r ctx rer q x VALID xupd UPD) as UPDVALID.
    rewrite UPD. simpl. rewrite Nat.sub_0_r.
    (* the s matcher itself is strictly nullable, we use that to go back to the inductive case *)
    assert (strictly_nullable_matcher s rer) as SNM by auto.
    match goal with
    | [ H:_ |- context[s ?x ?c]] => specialize (SN x c UPDVALID)
    end.
    destruct SN as [NONE | [y [VALIDy [END EQUAL]]]].
    { rewrite NONE. left. auto. }
    rewrite <- EQUAL.
    (* now we can apply the induction hypothesis since we're calling repeatMatcher' on a smaller min *)
    simpl in VALIDy. apply valid_input in VALIDy as VALIDyx.
    assert (FUELREC: fuel > min) by lia.
    match goal with
    | [H:_ |- context[repeatMatcher' s min ?max ?g ?y ?c ?lf ?wt ?fuel]] =>
        specialize (IHmin max fuel y c VALIDyx RER_ADEQUACY ROOT EARLY_ERRORS FUELREC SNM)
    end.
    destruct IHmin as [NONE | [z [VALIDz [ENDz EQUALz]]]].
    { rewrite NONE. auto. }
    rewrite <- EQUALz. right. exists z. split; auto.
    + assert (INPUT: input x = input y).
      { destruct VALIDy as [ONy _]. unfold OnInput in ONy. auto. }
      rewrite INPUT. auto.
    + split; auto. simpl in END. rewrite END. apply ENDz.
Qed.


(* main analysis correctness theorem *)
Theorem strictly_nullable_analysis_correct:
  forall (r:Regex) (root:Regex) (ctx:RegexContext) (rer:RegExpRecord) (dir:Direction) (m:Matcher)
    (STRICTLY_NULLABLE: strictly_nullable r = true)
    (COMPILE: compileSubPattern r ctx rer dir = Success m)
    (RER_ADEQUACY: countLeftCapturingParensWithin root nil = RegExpRecord.capturingGroupsCount rer)
    (ROOT: Root root (r, ctx))
    (EARLY_ERRORS: EarlyErrors.Pass_Regex root nil),
    strictly_nullable_matcher m rer.
Proof. Admitted.

End StriclyNullable.
