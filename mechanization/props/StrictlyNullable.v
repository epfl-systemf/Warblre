From Coq Require Import PeanoNat ZArith Bool Lia List.
From Warblre Require Import Tactics Focus Result Base Patterns Node StaticSemantics Notation List Semantics Match EarlyErrors RegExpRecord.

Import Notation.
Import Patterns.
Import Result.Notations.
Import Result.Notations.Boolean.
Import Coercions.
Import Semantics.
Import Notation.MatchState.
Import Match.
Import Correctness.MatchState.
Import Correctness.

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
  | Quantified r1 _ | Group _ r1 => strictly_nullable r1
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
      apply Correctness.CaptureRange.vCrUndefined.
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
      apply Correctness.CaptureRange.vCrUndefined.
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


(* main analysis correctness teorem *)
Theorem strictly_nullable_analysis_correct:
  forall (r:Regex) (root:Regex) (ctx:RegexContext) (rer:RegExpRecord) (dir:Direction) (m:Matcher)
    (STRICTLY_NULLABLE: strictly_nullable r = true)
    (COMPILE: compileSubPattern r ctx rer dir = Success m)
    (RER_ADEQUACY: countLeftCapturingParensWithin root nil = RegExpRecord.capturingGroupsCount rer)
    (ROOT: Root root (r, ctx))
    (EARLY_ERRORS: EarlyErrors.Pass_Regex root nil),
    strictly_nullable_matcher m rer.
Proof.
  intros r. induction r; intros root ctx rer dir m STRICTLY_NULLABLE COMPILE RER_ADEQUACY ROOT EARLY_ERRORS;
    try solve[inversion STRICTLY_NULLABLE]; unfold strictly_nullable_matcher; intros x c VALID;
    (* eapply MatcherInvariant.compileSubPattern with (str:=input x) in COMPILE as MATCHER_INV; eauto; *)
    simpl in COMPILE.
  (* empty *)
  - inversion COMPILE as [H]. clear H COMPILE.
    destruct (c x) eqn:CONT; auto.
    + destruct s; auto. right.
      exists x. split; auto.
    + right. exists x. split; auto.
  (* disjunction *)
  - simpl in COMPILE.
    inversion STRICTLY_NULLABLE as [SN12]. rewrite andb_true_iff in SN12. destruct SN12 as [SN1 SN2].
    clear STRICTLY_NULLABLE.
    destruct (compileSubPattern r1 (Disjunction_left r2 :: ctx) rer dir) as [m1|] eqn:SNM1; try solve[inversion COMPILE].
    apply IHr1 with (root:=root) in SNM1; auto. clear IHr1 SN1.
    destruct (compileSubPattern r2 (Disjunction_right r1 :: ctx) rer dir) as [m2|] eqn:SNM2; try solve[inversion COMPILE].
    apply IHr2 with (root:=root) in SNM2; auto. clear IHr2 SN2.
    inversion COMPILE as [M]. clear COMPILE M m.
    (* first, excecute m1 *)
    unfold strictly_nullable_matcher in SNM1.
    specialize (SNM1 x c VALID). destruct SNM1 as [TRYRIGHT | [y [VALIDy [SAMEIDX EQUAL]]]].
    +                           (* Matcher 1 failed, try matcher 2 *)
      rewrite TRYRIGHT. simpl. apply SNM2; auto.
    +                           (* Matcher 1 succeeded *)
      rewrite <- EQUAL.
      destruct (c y) as [res|] eqn:CONT.
      * cbn. destruct res as [ res| ]; cbn; auto. right.
        exists y. split; auto.
      * right. exists y. split; auto.
  (* quantifier *)
  - inversion STRICTLY_NULLABLE as [SN]. clear STRICTLY_NULLABLE.
    destruct (compileSubPattern r (Quantified_inner q :: ctx) rer dir) eqn:SNM; try solve[inversion COMPILE].
    apply IHr with (root:=root) in SNM; auto. clear IHr SN.
    inversion COMPILE as [M]. clear COMPILE M m.
    apply repeat_matcher_sn with (root:=root); auto.
    unfold repeatMatcherFuel. lia.
  (* concatenation *)
  - inversion STRICTLY_NULLABLE as [SN12]. rewrite andb_true_iff in SN12. destruct SN12 as [SN1 SN2].
    clear STRICTLY_NULLABLE.
    destruct (compileSubPattern r1 (Seq_left r2 :: ctx) rer dir) as [m1|] eqn:SNM1; try solve[inversion COMPILE].
    apply IHr1 with (root:=root) in SNM1; auto. clear IHr1 SN1.
    destruct (compileSubPattern r2 (Seq_right r1 :: ctx) rer dir) as [m2|] eqn:SNM2; try solve[inversion COMPILE].
    apply IHr2 with (root:=root) in SNM2; auto. clear IHr2 SN2.
    destruct dir eqn:DIR; inversion COMPILE as [M]. clear COMPILE M m.
    (* forward *)
    + specialize (SNM1 x (fun s => m2 s c) VALID). destruct SNM1 as [NONE | [y [VALIDy [SAMEIDX EQUAL]]]].
      * rewrite NONE. auto.
      * rewrite <- EQUAL.
        assert (SAMEINPUT: input x = input y).
        { destruct VALIDy as [Hy _]. unfold OnInput in Hy. auto. }
        rewrite SAMEINPUT. rewrite SAMEIDX. apply SNM2. rewrite <- SAMEINPUT. auto.
    (* backward *)
    + specialize (SNM2 x (fun s => m1 s c) VALID). destruct SNM2 as [NONE | [y [VALIDy [SAMEIDX EQUAL]]]].
      * rewrite NONE. auto.
      * rewrite <- EQUAL.
        assert (SAMEINPUT: input x = input y).
        { destruct VALIDy as [Hy _]. unfold OnInput in Hy. auto. }
        rewrite SAMEINPUT. rewrite SAMEIDX. apply SNM1. rewrite <- SAMEINPUT. auto.
  (* capture group *)
  - inversion STRICTLY_NULLABLE as [SN]. clear STRICTLY_NULLABLE.
    destruct (compileSubPattern r (Group_inner name :: ctx) rer dir) eqn:SNM; try solve[inversion COMPILE].
    apply IHr with (root:=root) in SNM; auto. clear IHr SN.
    inversion COMPILE as [M]. clear COMPILE M m.
    match goal with
    | [ x:MatchState |- context[?s x ?c = _]] => specialize (SNM x c)
    end.
    destruct SNM as [NONE | [y [VALIDy [SAMEIDX EQUAL]]]]. auto.
    (* Mismatch inside the group *)
    { rewrite <- NONE. auto. }
    (* a match is found, and the captures are updated *)
    rewrite <- EQUAL. clear EQUAL. rewrite SAMEIDX. rewrite Z.leb_refl. simpl.
    assert (NOFAIL: countLeftCapturingParensBefore (Group name r) ctx + 1 =? O = false).
    { rewrite Nat.eqb_neq. lia. }
    rewrite NOFAIL. rewrite Nat.add_sub.
    (* the update is independent of the direction *)
    match goal with
    | [ |- context[(if ?c then ?i else ?e)]] => replace (if c then i else e) with e
    end.
    2: { destruct dir; auto. } simpl.
    destruct (List.Update.Nat.One.update (CaptureRange_or_undefined (CaptureRange.make (endIndex y) (endIndex y))) (captures y) (countLeftCapturingParensBefore (Group name r) ctx)) eqn:UPD.
    + right. exists (match_state (input x) (endIndex y) s0). split; auto.
      rewrite <- SAMEIDX. apply change_captures with (cap:=captures x); auto.
      * apply List.Update.Nat.One.success_length in UPD. rewrite <- UPD.
        destruct VALIDy as [_ [_ [LEN _]]]. auto.
      * destruct VALIDy as [ON [ITER [LEN FORALL]]].
        eapply List.Update.Nat.One.prop_preservation; eauto.
        apply CaptureRange.vCrDefined; auto. lia.
    (* the capture update cannot fail *)
    + apply List.Update.Nat.One.failure_bounds in UPD.
      pose proof (EarlyErrors.countLeftCapturingParensBefore_contextualized _ _ _ ROOT EARLY_ERRORS) as PLUSLE.
      unfold countLeftCapturingParensBefore,countLeftCapturingParensWithin in *. cbn in *. MatchState.solve_with lia.
  (* InputStart *)
  - inversion COMPILE as [M]. clear COMPILE M.
    destruct (endIndex x =? 0)%Z eqn:START.
    (* start of line *)
    { right. exists x. auto. }
    destruct (RegExpRecord.multiline rer) eqn:MULTI.
    (* not multi line *)
    2: { left. auto. }
    (* accessing the string cannot fail *)
    simpl. assert (NOFAILURE: (0 <= (endIndex x - 1) < length (input x))%Z).
    { destruct VALID as [_ [ITER _]]. unfold IteratorOn in ITER. split; lia. }
    destruct (List.Indexing.Int.indexing (input x) (endIndex x - 1)) eqn:INDEX.    
    2: { rewrite <- List.Indexing.Int.success_bounds0 in NOFAILURE. rewrite INDEX in NOFAILURE. destruct NOFAILURE. inversion H. }
    simpl. destruct (CharSet.contains Characters.line_terminators s) eqn:TERMINATOR.
    + right. exists x. auto.
    + left. auto.
  (* InputEnd *)
  - inversion COMPILE as [M]. clear COMPILE M.
    destruct (endIndex x =? (length (input x)))%Z eqn:END.
    (* end of line *)
    { right. exists x. auto. }
    destruct (RegExpRecord.multiline rer) eqn:MULTI.
    (* not multi line *)
    2: { left. auto. }
    (* accessing the string cannot fail *)
    simpl. assert (NOFAILURE: (0 <= (endIndex x) < length (input x))%Z).
    { destruct VALID as [_ [ITER _]]. unfold IteratorOn in ITER. split; lia. }
    destruct (List.Indexing.Int.indexing (input x) (endIndex x)) eqn:INDEX.    
    2: { rewrite <- List.Indexing.Int.success_bounds0 in NOFAILURE. rewrite INDEX in NOFAILURE. destruct NOFAILURE. inversion H. }
    simpl. destruct (CharSet.contains Characters.line_terminators s) eqn:TERMINATOR.
    + right. exists x. auto.
    + left. auto.
  (* WordBoundary *)
  - inversion COMPILE as [M]. clear COMPILE M.
    apply isWordsuccess in VALID as H. destruct H as [v1 WORD1]. rewrite WORD1.
    apply isWordsuccess_minusone in VALID as H. destruct H as [v2 WORD2]. rewrite WORD2.
    destruct v1; destruct v2; eauto.
  (* NotWordBoundary *)
  - inversion COMPILE as [M]. clear COMPILE M.
    apply isWordsuccess in VALID as H. destruct H as [v1 WORD1]. rewrite WORD1.
    apply isWordsuccess_minusone in VALID as H. destruct H as [v2 WORD2]. rewrite WORD2.
    destruct v1; destruct v2; eauto.
  (* Lookahead *)
  - destruct (compileSubPattern r (Lookahead_inner :: ctx) rer forward) eqn:SNM; try solve[inversion COMPILE].
    eapply MatcherInvariant.compileSubPattern in SNM as LOOK_INV; eauto.
    inversion COMPILE as [M]. clear COMPILE M m.
    specialize (LOOK_INV x (fun y => y) VALID). destruct LOOK_INV as [NONE | [y [VALIDy [PROGRESS EQUAL]]]].
    { rewrite NONE. auto. }
    rewrite <- EQUAL. simpl.
    right. exists (match_state (input x) (endIndex x) (captures y)). split; auto.
    apply valid_trans with (x:=x) (y:=y); auto.
  (* NegativeLookahead *)
  - destruct (compileSubPattern r (NegativeLookahead_inner :: ctx) rer forward) eqn:SNM; try solve[inversion COMPILE].
    eapply MatcherInvariant.compileSubPattern in SNM as LOOK_INV; eauto.
    inversion COMPILE as [M]. clear COMPILE M m.
    specialize (LOOK_INV x (fun y => y) VALID). destruct LOOK_INV as [NONE | [y [VALIDy [PROGRESS EQUAL]]]].
    2: { rewrite <- EQUAL. auto. }
    rewrite NONE. simpl.
    right. exists x. split; auto.
  (* Lookbehind *)
  - destruct (compileSubPattern r (Lookbehind_inner :: ctx) rer backward) eqn:SNM; try solve[inversion COMPILE].
    eapply MatcherInvariant.compileSubPattern in SNM as LOOK_INV; eauto.
    inversion COMPILE as [M]. clear COMPILE M m.
    specialize (LOOK_INV x (fun y => y) VALID). destruct LOOK_INV as [NONE | [y [VALIDy [PROGRESS EQUAL]]]].
    { rewrite NONE. auto. }
    rewrite <- EQUAL. simpl.
    right. exists (match_state (input x) (endIndex x) (captures y)). split; auto.
    apply valid_trans with (x:=x) (y:=y); auto.
    (* NegativeLookbehind *)
  - destruct (compileSubPattern r (NegativeLookbehind_inner :: ctx) rer backward) eqn:SNM; try solve[inversion COMPILE].
    eapply MatcherInvariant.compileSubPattern in SNM as LOOK_INV; eauto.
    inversion COMPILE as [M]. clear COMPILE M m.
    specialize (LOOK_INV x (fun y => y) VALID). destruct LOOK_INV as [NONE | [y [VALIDy [PROGRESS EQUAL]]]].
    2: { rewrite <- EQUAL. auto. }
    rewrite NONE. simpl.
    right. exists x. split; auto.
Qed.


(** * Repeating a strictly nullable matcher does nothing *)

Lemma strictly_nullable_repeatmatcher':
  forall (r:Regex) (root:Regex) (ctx:RegexContext) (rer:RegExpRecord) (dir:Direction) (m:Matcher)
    (STRICTLY_NULLABLE: strictly_nullable r = true)
    (COMPILE: compileSubPattern r ctx rer dir = Success m)
    (RER_ADEQUACY: countLeftCapturingParensWithin root nil = RegExpRecord.capturingGroupsCount rer)
    (ROOT: Root root (r, ctx))
    (EARLY_ERRORS: EarlyErrors.Pass_Regex root nil),
  forall (x:MatchState) (c:MatcherContinuation)
    (VALID: Valid (input x) rer x),
    repeatMatcher' m O%nat NoI.Inf true x c (countLeftCapturingParensBefore r ctx) (countLeftCapturingParensWithin r ctx) (repeatMatcherFuel O%nat x) = c x.
Proof.
  intros r root ctx rer dir m STRICTLY_NULLABLE COMPILE RER_ADEQUACY ROOT EARLY_ERRORS x c VALID.
  apply strictly_nullable_analysis_correct with (ctx:=ctx) (rer:=rer) (dir:=dir) (m:=m) (root:=root) in STRICTLY_NULLABLE; auto.
  (* we know that we have enouh fuel to do a single iteration *)
  destruct (repeatMatcherFuel 0 x) eqn:FUEL; try solve[unfold repeatMatcherFuel in FUEL; lia].
  simpl. repeat rewrite PeanoNat.Nat.add_sub.
  (* capture reset cannot fail and preserves validity *)
  pose proof (capture_reset_validity r root ctx rer RER_ADEQUACY ROOT EARLY_ERRORS) as CAP_VALID.
  pose proof (capture_reset_success r ctx rer x VALID CAP_VALID) as [xupd UPD]. rewrite UPD.
  pose proof (capture_reset_preserve_validity r ctx rer x VALID xupd UPD) as UPDVALID.
  unfold strictly_nullable_matcher in STRICTLY_NULLABLE.
  specialize (STRICTLY_NULLABLE (match_state (input x) (endIndex x) xupd)
              (fun y : MatchState =>
       if (endIndex y =? endIndex x)%Z
       then None
       else
        repeatMatcher' m 0 +∞ true y c (countLeftCapturingParensBefore r ctx)
                              (countLeftCapturingParensWithin r ctx) n) UPDVALID).
  cbn. destruct STRICTLY_NULLABLE as [MISMATCH | [y [VALIDy [SAMEIDX EQUAL]]]].
  - rewrite MISMATCH. auto.
  - rewrite <- EQUAL. simpl in SAMEIDX. rewrite SAMEIDX. rewrite Z.eqb_refl. auto.
Qed.


(** * Transformation correctness: Switching a strictly nullable regex starred for a n empty is correct  *)

Theorem strictly_nullable_same_matcher:
  forall (r:Regex) (root:Regex) (ctx:RegexContext) (rer:RegExpRecord) (dir:Direction) (mstar:Matcher) (mempty:Matcher)
    (STRICTLY_NULLABLE: strictly_nullable r = true)
    (COMPILESTAR: compileSubPattern (Quantified r (Greedy Star)) ctx rer dir = Success mstar)
    (COMPILEEMPTY: compileSubPattern Empty ctx rer dir = Success mempty)
    (RER_ADEQUACY: countLeftCapturingParensWithin root nil = RegExpRecord.capturingGroupsCount rer)
    (ROOT: Root root (r, Quantified_inner (Greedy Star) :: ctx))
    (EARLY_ERRORS: EarlyErrors.Pass_Regex root nil),
  forall (x:MatchState) (c:MatcherContinuation) (VALID: Valid (input x) rer x),
    mstar x c = mempty x c.
Proof.
  intros r root ctx rer dir mstar mempty STRICTLY_NULLABLE COMPILESTAR COMPILEEMPTY RER_ADEQUACY ROOT EARLY_ERRORS x c VALID.
  simpl in COMPILEEMPTY. unfold Coercions.wrap_Matcher in COMPILEEMPTY. inversion COMPILEEMPTY. clear COMPILEEMPTY H0 mempty.
  simpl in COMPILESTAR. destruct (compileSubPattern r (Quantified_inner (Greedy Star) :: ctx) rer dir) as [m|] eqn:SUBSTAR.
  2: { inversion COMPILESTAR. }
  unfold Coercions.wrap_Matcher in COMPILESTAR. inversion COMPILESTAR as [STAR]. clear COMPILESTAR.
  apply strictly_nullable_repeatmatcher' with (x:=x) (c:=c) (root:=root) in SUBSTAR; auto.
  simpl in SUBSTAR. rewrite PeanoNat.Nat.add_0_r in SUBSTAR.
  unfold repeatMatcher. rewrite SUBSTAR. auto.
Qed.
End StriclyNullable.
