From Coq Require Import PeanoNat List Lia Program.Equality.
From Warblre Require Import Tactics List Result Focus Base Patterns StaticSemantics.

Module EarlyErrors.

  Inductive SingletonCharacterEscape: CharacterEscape -> Character -> Prop :=
  | Singleton_ctrl_t: SingletonCharacterEscape (CharacterEscape.ControlEsc ControlEscape.t) Character.CHARACTER_TABULATION
  | Singleton_ctrl_n: SingletonCharacterEscape (CharacterEscape.ControlEsc ControlEscape.n) Character.LINE_FEED
  | Singleton_ctrl_v: SingletonCharacterEscape (CharacterEscape.ControlEsc ControlEscape.v) Character.LINE_TABULATION
  | Singleton_ctrl_f: SingletonCharacterEscape (CharacterEscape.ControlEsc ControlEscape.f) Character.FORM_FEED
  | Singleton_ctrl_r: SingletonCharacterEscape (CharacterEscape.ControlEsc ControlEscape.r) Character.CARRIAGE_RETURN
  | Singleton_zero: SingletonCharacterEscape CharacterEscape.Zero Character.NULL
  | Singleton_id: forall c, SingletonCharacterEscape (CharacterEscape.IdentityEsc c) c.

  Inductive SingletonClassAtom: ClassAtom -> Character -> Prop :=
  | Singleton_SourceCharacter: forall c, SingletonClassAtom (SourceCharacter c) c
  | Singleton_b: SingletonClassAtom (ClassEsc ClassEscape.b) Character.BACKSPACE
  | Singleton_dash: SingletonClassAtom (ClassEsc ClassEscape.Dash) Character.HYPHEN_MINUS
  | Singleton_char_esc: forall ce c,
      SingletonCharacterEscape ce c -> SingletonClassAtom (ClassEsc (ClassEscape.CharacterEsc ce)) c.

  Inductive ClassRanges: Patterns.ClassRanges -> Prop :=
  | EmptyCR: ClassRanges Patterns.EmptyCR
  | ClassAtomCR: forall ca t, ClassRanges t -> ClassRanges (Patterns.ClassAtomCR ca t)
  | RangeCR: forall l h cl ch t,
      SingletonClassAtom l cl ->
      SingletonClassAtom h ch ->
      (Character.numeric_value cl <= Character.numeric_value ch)%nat ->
      ClassRanges t ->
      ClassRanges (Patterns.RangeCR l h t).

  Module Pass.
    Inductive CharClass: Patterns.CharClass -> Prop :=
    | NoninvertedCC: forall crs, ClassRanges crs -> CharClass (Patterns.NoninvertedCC crs)
    | InvertedCC: forall crs, ClassRanges crs -> CharClass (Patterns.InvertedCC crs).

    Inductive AtomEscape: Patterns.AtomEscape -> RegexContext -> Prop :=
    | DecimalEsc: forall ctx n, (positive_to_non_neg n) <= (countLeftCapturingParensWithin (zip (AtomEsc (Patterns.AtomEscape.DecimalEsc n)) ctx) (nil)) -> AtomEscape (Patterns.AtomEscape.DecimalEsc n) ctx
    | CharacterClassEsc: forall ctx esc, AtomEscape (Patterns.AtomEscape.CharacterClassEsc esc) ctx
    | CharacterEsc: forall ctx esc, AtomEscape (Patterns.AtomEscape.CharacterEsc esc) ctx
    | GroupEsc: forall ctx gn, List.length (groupSpecifiersThatMatch (AtomEsc (Patterns.AtomEscape.GroupEsc gn)) ctx gn) = 1 -> AtomEscape (Patterns.AtomEscape.GroupEsc gn) ctx.

    Inductive QuantifierPrefix: Patterns.QuantifierPrefix -> Prop :=
    | Star: QuantifierPrefix Patterns.Star
    | Plus: QuantifierPrefix Patterns.Plus
    | Question: QuantifierPrefix Patterns.Question
    | RepExact: forall n, QuantifierPrefix (Patterns.RepExact n)
    | RepPartialRange: forall n, QuantifierPrefix (Patterns.RepPartialRange n)
    | RepRange: forall min max, (min <= max)%nat -> QuantifierPrefix (Patterns.RepRange min max).

    Inductive Quantifier: Patterns.Quantifier -> Prop :=
    | Greedy: forall p, QuantifierPrefix p -> Quantifier (Patterns.Greedy p)
    | Lazy: forall p, QuantifierPrefix p -> Quantifier (Patterns.Lazy p).

    Inductive Regex: Patterns.Regex -> RegexContext -> Prop :=
    | Empty: forall ctx, Regex Patterns.Empty ctx
    | Char: forall chr ctx, Regex (Patterns.Char chr) ctx
    | Dot: forall ctx, Regex Patterns.Dot ctx
    | AtomEsc: forall esc ctx, AtomEscape esc ctx -> Regex (Patterns.AtomEsc esc) ctx
    | CharacterClass: forall cc ctx, CharClass cc -> Regex (Patterns.CharacterClass cc) ctx
    | Disjunction: forall r1 r2 ctx, Regex r1 (Disjunction_left r2 :: ctx) -> Regex r2 (Disjunction_right r1 :: ctx) -> Regex (Patterns.Disjunction r1 r2) ctx
    | Quantified: forall r q ctx, Regex r (Quantified_inner q :: ctx) -> Quantifier q -> Regex (Patterns.Quantified r q) ctx
    | Seq: forall r1 r2 ctx, Regex r1 (Seq_left r2 :: ctx) -> Regex r2 (Seq_right r1 :: ctx) -> Regex (Patterns.Seq r1 r2) ctx
    | Group: forall name r ctx, Regex r (Group_inner name :: ctx) -> Regex (Patterns.Group name r) ctx
    | AssertInputStart: forall ctx, Regex Patterns.AssertInputStart ctx
    | AssertInputEnd: forall ctx, Regex Patterns.AssertInputEnd ctx
    | AssertWordBoundary: forall ctx, Regex Patterns.AssertWordBoundary ctx
    | AssertNotWordBoundary: forall ctx, Regex Patterns.AssertNotWordBoundary ctx
    | Lookahead: forall r ctx, Regex r (Lookahead_inner :: ctx) -> Regex (Patterns.Lookahead r) ctx
    | NegativeLookahead: forall r ctx, Regex r (NegativeLookahead_inner :: ctx) -> Regex (Patterns.NegativeLookahead r) ctx
    | Lookbehind: forall r ctx, Regex r (Lookbehind_inner :: ctx) -> Regex (Patterns.Lookbehind r) ctx
    | NegativeLookbehind: forall r ctx, Regex r (NegativeLookbehind_inner :: ctx) -> Regex (Patterns.NegativeLookbehind r) ctx.
  End Pass.

  Lemma countLeftCapturingParensBefore_contextualized: forall ctx f r,
    Root r f ctx ->
    Pass.Regex r nil ->
    (countLeftCapturingParensBefore f ctx) + (countLeftCapturingParensWithin f ctx) <= countLeftCapturingParensWithin r nil.
  Proof.
    unfold Root.
    induction ctx; intros f r R_r EEP_r.
    - rewrite -> Zip.id in R_r. subst. cbn. lia.
    - unfold countLeftCapturingParensBefore,countLeftCapturingParensWithin in *.
      destruct a; try solve [
        cbn in *;
        lazymatch goal with
        | [ _: r = zip ?r' ctx |- _ + ?n0 + ?n1 <= _ ] => assert (n0 + n1 <= countLeftCapturingParensWithin_impl r')%nat by (cbn; lia)
        end;
        specialize (IHctx _ _ ltac:(eassumption) ltac:(eassumption)); lia ].
  Qed.

  Lemma groupSpecifiersThatMatch_is_filter_map {F: Type} {_: Result.AssertionError F}: forall r ctx gn, exists f,
    (forall i j, f i = f j -> i = j) /\
    (forall i r' ctx', List.Indexing.Nat.indexing (groupSpecifiersThatMatch r ctx gn) i = Success (r', ctx') ->
    exists ctx'',
      Group_inner (Some gn) :: ctx'' = ctx' /\
      List.Indexing.Nat.indexing (Zip.Walk.walk (zip r ctx) nil) (f i) = Success (Group (Some gn) r', ctx'')).
  Proof.
    unfold groupSpecifiersThatMatch.
    intros r ctx gn. generalize dependent (Zip.Walk.walk (zip r ctx) nil). clear r. clear ctx.
    induction l as [| [rh ctxh] l' (f' & H0 & H1) ].
    - exists (fun x => x). split.
      + intros i j <-. reflexivity.
      + intros i r' ctx' Eq_indexed. cbn in Eq_indexed. rewrite -> List.Indexing.Nat.nil in Eq_indexed. Result.assertion_failed_helper.
    - let direct_recursion := solve [ exists (fun i => S (f' i)); setoid_rewrite -> Nat.succ_inj_wd; split; try assumption ] in
        destruct rh; try direct_recursion;
        destruct name as [ name | ]; try direct_recursion;
        cbn; destruct (name =? capturingGroupName gn)%GrName eqn:Eq_gs_gn; try direct_recursion.
      exists (fun i => if Nat.eqb i 0 then 0 else S (f' (i - 1))).
      split.
      + intros i j H. destruct (Nat.eqb i 0) eqn:Eq_i; destruct (Nat.eqb j 0) eqn:Eq_j; spec_reflector Nat.eqb_spec; subst.
        * reflexivity. * discriminate. * discriminate. * apply Nat.succ_inj in H. specialize H0 with (1 := H). lia.
      + intros [| i] r' ctx'; cbn.
        * cbn. subst. intros [=<-<-]. exists ctxh. split; reflexivity.
        * rewrite -> List.Indexing.Nat.cons. rewrite -> Nat.sub_0_r. apply H1.
  Qed.

  Lemma groupSpecifiersThatMatch_too_big_cause {F: Type} {_: Result.AssertionError F}: forall r ctx gn,
    (List.length (groupSpecifiersThatMatch r ctx gn) >= 2)%nat ->
    exists i j ri ctxi rj ctxj,
      i <> j /\
      List.Indexing.Nat.indexing (Zip.Walk.walk (zip r ctx) nil) i = Success (Group (Some gn) ri, ctxi) /\
      List.Indexing.Nat.indexing (Zip.Walk.walk (zip r ctx) nil) j = Success (Group (Some gn) rj, ctxj).
  Proof.
    intros r ctx gn B_length.
    assert (exists v w, List.Indexing.Nat.indexing (groupSpecifiersThatMatch r ctx gn) 0 = Success v /\ List.Indexing.Nat.indexing (groupSpecifiersThatMatch r ctx gn) 1 = Success w)
        as ([ r0 ctx0 ] & [ r1 ctx1 ] & Eq_indexed_0 & Eq_indexed_1). {
      destruct (groupSpecifiersThatMatch r ctx gn) as [ | h0 [ | h1 ? ]] eqn:Eq; try solve [ cbn in B_length; lia ].
      exists h0. exists h1. split; reflexivity.
    }
    pose proof (groupSpecifiersThatMatch_is_filter_map r ctx gn) as (f & Inj_f & Def_f).
    pose proof (Def_f _ _ _ Eq_indexed_0) as (? & ? & ?).
    pose proof (Def_f _ _ _ Eq_indexed_1) as (? & ? & ?).
    exists (f 0). exists (f 1). do 4 eexists. split; [ | repeat (split; [ eassumption | ]); eassumption ].
    destruct (Nat.eq_dec (f 0) (f 1)) as [ Eq_f |]; try assumption.
    specialize Inj_f with (1 := Eq_f). discriminate.
  Qed.

  Lemma groupSpecifiersThatMatch_head_is_group: forall r0 ctx0 gn r ctx t, groupSpecifiersThatMatch r0 ctx0 gn = (r, ctx) :: t ->
    0 < countLeftCapturingParensBefore r ctx /\
    exists ctx', ctx = Group_inner (Some gn) :: ctx'.
  Proof.
    intros r0 ctx0 gn r ctx t H.
    unfold groupSpecifiersThatMatch in H.
    generalize dependent (Zip.Walk.walk (zip r0 ctx0) nil). clear r0. clear ctx0.
    induction l as [ | h t' ]; intros H.
    - discriminate.
    - cbn in H. destruct h as [ h_r h_ctx ].
      destruct h_r; try destruct name as [ name | ]; try solve [ cbn in H; apply (IHt' H) ].
      destruct (GroupName.eqs name (capturingGroupName gn)).
      + cbn in H. subst. injection H as <-. split.
        * subst. cbn. lia.
        * exists h_ctx. symmetry. assumption.
      + cbn in H. apply (IHt' H).
  Qed.

  Lemma groupSpecifiersThatMatch_singleton {_: Result.AssertionError SyntaxError}: forall r name,
      List.Exists.exist (Zip.Walk.walk r nil) (fun node0 =>
        List.Exists.exist (Zip.Walk.walk r nil) (fun node1 =>
          if RegexNode.eqs node0 node1 then Success false
          else
            let (r0, ctx0) := node0 in
            let (r1, ctx1) := node1 in
            match r0, r1 with
            | Group (Some name0) _, Group (Some name1) _ => Success (GroupName.eqb name0 name1)
            | _, _ => Success false
            end))
        = @Success _ SyntaxError false ->
      (List.length (groupSpecifiersThatMatch r nil name) <= 1)%nat.
  Proof.
    intros r name Ex.
    destruct (Compare_dec.lt_dec (List.length (groupSpecifiersThatMatch r nil name)) 2) as [ Ineq | Ineq ].
    - lia.
    - apply Compare_dec.not_lt in Ineq. apply groupSpecifiersThatMatch_too_big_cause in Ineq as (i & j & ri & ctxi & rj & ctxj & Ineq_ij & Eq_indexed_i & Eq_indexed_j).
      rewrite -> Zip.id in *.
      apply List.Exists.false_to_prop in Ex. specialize (Ex _ _ Eq_indexed_i).
      apply List.Exists.false_to_prop in Ex. specialize (Ex _ _ Eq_indexed_j). cbn beta in Ex.
      focus § _ [] _ § auto destruct in Ex.
      + injection e as <- <-. pose proof Zip.Walk.uniqueness as Falsum. specialize Falsum with (1 := Eq_indexed_i) (2 := Eq_indexed_j). contradiction.
      + unfold GroupName.eqb in *. destruct (GroupName.eqs name name) eqn:Falsum. * discriminate. * contradiction.
  Qed.

  Lemma isCharacterClass_singleton {F: Type} {_: Result.AssertionError F}: forall c, isCharacterClass c = false -> exists v, SingletonClassAtom c v.
  Proof.
    intros [ ]; cbn.
    - eexists; repeat econstructor.
    - destruct esc; try discriminate; intros _.
      + eexists. econstructor.
      + eexists. econstructor.
      + destruct esc.
        * destruct esc; eexists; do 3 econstructor.
        * eexists; do 2 econstructor.
        * eexists; do 2 econstructor.
  Qed.

  Lemma characterValue_singleton {F: Type} {_: Result.AssertionError F}: forall c v, characterValue c = @Success _ F (Character.numeric_value v) <-> SingletonClassAtom c v.
  Proof.
    intros c v; split; intros H; (repeat match goal with
      | [ c: ClassAtom |- _] => destruct c
      | [ c: ClassEscape |- _] => destruct c
      | [ c: CharacterEscape |- _] => destruct c
      | [ c: CharacterClassEscape |- _] => destruct c
      | [ c: ControlEscape |- _] => destruct c
      | [ S: SingletonClassAtom _ _ |- _ ] => dependent destruction S
      | [ S: SingletonCharacterEscape _ _ |- _ ] => dependent destruction S
      end); try solve [ cbn in H; injection H as Eq; apply Character.numeric_inj in Eq as <-; repeat constructor | Result.assertion_failed_helper | reflexivity ].
  Qed.

  Module Safety.

    Lemma characterValue: forall ca, isCharacterClass ca = false -> characterValue ca <> Failure SyntaxError.AssertionFailed.
    Proof.
      intros ca H.
      destruct ca; Result.assertion_failed_helper.
      destruct esc; Result.assertion_failed_helper.
      destruct esc; Result.assertion_failed_helper.
      destruct esc; Result.assertion_failed_helper.
    Qed.

    Lemma class_ranges: forall c, earlyErrors_class_ranges c <> Failure SyntaxError.AssertionFailed.
    Proof.
      induction c; Result.assertion_failed_helper.
      cbn. focus § _ (_ [] _) § auto destruct; subst; focus § _ [] _ § auto destruct in AutoDest_0; try easy;
        repeat lazymatch goal with
        | [ f: SyntaxError |- _ ] => destruct f
        | [ _: context[ if ?b then _ else _ ] |- _ ] => destruct b eqn:?Eq
        | [ H0: isCharacterClass ?c = false, H1: StaticSemantics.characterValue ?c = Failure SyntaxError.AssertionFailed |- _ ] => exfalso; apply (characterValue _ H0 H1)
        end; boolean_simplifier; try discriminate.
    Qed.

    Definition char_class: forall cc, earlyErrors_char_class cc <> Failure SyntaxError.AssertionFailed.
    Proof. destruct cc; cbn; apply class_ranges. Qed.

    Lemma rec: forall r ctx, earlyErrors_rec r ctx <> Failure SyntaxError.AssertionFailed.
    Proof.
      induction r; intros ctx H; cbn in H; Result.assertion_failed_helper.
      - focus § _ [] _ § auto destruct in H.
      - apply (char_class _ H).
      - focus § _ [] _ § auto destruct in H; subst. + apply (IHr2 _ H). + destruct f. apply (IHr1 _ AutoDest_).
      - focus § _ [] _ § auto destruct in H. Result.assertion_failed_helper. apply (IHr _ AutoDest_).
      - focus § _ [] _ § auto destruct in H; subst. + apply (IHr2 _ H). + destruct f. apply (IHr1 _ AutoDest_).
      - apply (IHr _ H).
      - apply (IHr _ H).
      - apply (IHr _ H).
      - apply (IHr _ H).
      - apply (IHr _ H).
    Qed.

    Lemma earlyErrors: forall r, earlyErrors r nil <> Failure SyntaxError.AssertionFailed.
    Proof.
      intros r H. unfold earlyErrors in H. focus § _ [] _ § auto destruct in H.
      - apply (rec _ _ H).
      - Result.assertion_failed_helper.
        apply List.Exists.failure_kind in AutoDest_ as (_ & ? & _ & H).
        apply List.Exists.failure_kind in H as (_ & ? & _ & H).
        focus § _ [] _ § auto destruct in H.
    Qed.
  End Safety.

  Module Completeness.
    Lemma isCharacterClass_false: forall a, isCharacterClass a = false -> exists c, SingletonClassAtom a c.
    Proof.
      intros a Eq. repeat match goal with
        | [ c: ClassAtom |- _] => destruct c
        | [ c: ClassEscape |- _] => destruct c
        | [ c: CharacterEscape |- _] => destruct c
        | [ c: CharacterClassEscape |- _] => destruct c
        | [ c: ControlEscape |- _] => destruct c
        end; cbn in Eq; try solve [ discriminate | eexists; repeat econstructor ].
    Qed.

    Lemma class_ranges: forall c,
      earlyErrors_class_ranges c = Success false ->
      ClassRanges c.
    Proof.
      induction c; intros H; cbn in *.
      - constructor.
      - constructor. apply IHc. apply H.
      - focus § _ [] _ § auto destruct in H. boolean_simplifier. focus § _ [] _ § auto destruct in AutoDest_0. subst. injection AutoDest_0 as ?.
        apply isCharacterClass_false in H0 as (cl & ?). apply isCharacterClass_false in H1 as (ch & ?).
        apply RangeCR with (cl := cl) (ch := ch); try assumption.
        + destruct s1;
            repeat match goal with
            | [ H: SingletonClassAtom ?c ?cc, G: characterValue ?c = _ |- _ ] => rewrite <- (@characterValue_singleton) in H; rewrite -> H in *; injection G as ->
            end; try spec_reflector Nat.leb_spec0; try lia.
        + apply IHc. apply H.
    Qed.

    Definition char_class: forall cc, earlyErrors_char_class cc = Success false -> Pass.CharClass cc.
    Proof. intros; destruct cc; constructor; apply class_ranges; assumption. Qed.

    Definition quantifier_prefix: forall q, earlyErrors_quantifier_prefix q = false -> Pass.QuantifierPrefix q.
    Proof. intros; destruct q; constructor. cbn in H. destruct min as [ ] eqn:Eq_min. - lia. - destruct (max <=? n) eqn:Ineq; spec_reflector Nat.leb_spec0; lia. Qed.


    Definition quantifier: forall q, earlyErrors_quantifier q = false -> Pass.Quantifier q.
    Proof. intros; destruct q; constructor; apply quantifier_prefix; assumption. Qed.

    Lemma rec: forall root r ctx,
        List.Exists.exist (Zip.Walk.walk root nil) (fun node0 =>
          List.Exists.exist (Zip.Walk.walk root nil) (fun node1 =>
            if RegexNode.eqs node0 node1 then Success false
            else
              let (r0, ctx0) := node0 in
              let (r1, ctx1) := node1 in
              match r0, r1 with
              | Group (Some name0) _, Group (Some name1) _ => Success (GroupName.eqb name0 name1)
              | _, _ => Success false
              end))
          = @Success _ SyntaxError false ->
      Root root r ctx ->
      earlyErrors_rec r ctx = Success false ->
      Pass.Regex r ctx.
    Proof.
      intros root. induction r; intros ctx RP Root_r EE_r.
      - constructor.
      - constructor.
      - constructor.
      - constructor. destruct ae; cbn in EE_r; constructor.
        + focus § _ [] _ § auto destruct in EE_r. unfold capturingGroupNumber,positive_to_non_neg,positive_to_nat in *. focus § _ [] _ § auto destruct in AutoDest_.
          * lia.
          * spec_reflector Nat.leb_spec0. lia.
        + focus § _ [] _ § auto destruct in EE_r. spec_reflector Nat.eqb_spec.
          pose proof (groupSpecifiersThatMatch_singleton _ id RP).
          unfold groupSpecifiersThatMatch in *. rewrite <- Root_r in *.
          rewrite -> Zip.id in *.
          lia.
      - constructor. apply char_class. apply EE_r.
      - constructor.
        + cbn in EE_r. focus § _ [] _ § auto destruct in EE_r. apply IHr1; try assumption.
        + cbn in EE_r. focus § _ [] _ § auto destruct in EE_r. apply IHr2; try assumption.
      - constructor. cbn in EE_r. focus § _ [] _ § auto destruct in EE_r. apply IHr; try assumption.
        apply quantifier.
        cbn in EE_r. focus § _ [] _ § auto destruct in EE_r. injection EE_r as EE_r. apply EE_r.
      - constructor.
        + cbn in EE_r. focus § _ [] _ § auto destruct in EE_r. apply IHr1; try assumption.
        + cbn in EE_r. focus § _ [] _ § auto destruct in EE_r. apply IHr2; try assumption.
      - constructor. cbn in EE_r. focus § _ [] _ § auto destruct in EE_r. apply IHr; try assumption.
      - constructor.
      - constructor.
      - constructor.
      - constructor.
      - constructor. cbn in EE_r. focus § _ [] _ § auto destruct in EE_r. apply IHr; try assumption.
      - constructor. cbn in EE_r. focus § _ [] _ § auto destruct in EE_r. apply IHr; try assumption.
      - constructor. cbn in EE_r. focus § _ [] _ § auto destruct in EE_r. apply IHr; try assumption.
      - constructor. cbn in EE_r. focus § _ [] _ § auto destruct in EE_r. apply IHr; try assumption.
      Qed.

    Lemma earlyErrors: forall r, earlyErrors r nil = Success false -> Pass.Regex r nil.
    Proof.
      intros r H. unfold earlyErrors in H. focus § _ [] _ § auto destruct in H. apply rec with (root := r); solve [ assumption | reflexivity ].
    Qed.
  End Completeness.
End EarlyErrors.