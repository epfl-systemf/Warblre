From Coq Require Import PeanoNat List Lia NArith Program.Equality.
From Warblre Require Import Tactics List Result Focus Base Characters Patterns Node StaticSemantics.

Section EarlyErrors.
  Context {Σ} `{ep: CharacterInstance Σ}.
    Import Patterns.

  Notation hex4digitsValue v := (let (_0, _1, _2, _3) := v in HexDigit.to_integer (_0 :: _1 :: _2 :: _3 :: nil)) (only parsing).

  Inductive SingletonCharacterEscape: CharacterEscape -> non_neg_integer -> Prop :=
  | Singleton_ctrl_t: SingletonCharacterEscape (ControlEsc esc_t) (Character.numeric_value Characters.CHARACTER_TABULATION)
  | Singleton_ctrl_n: SingletonCharacterEscape (ControlEsc esc_n) (Character.numeric_value Characters.LINE_FEED)
  | Singleton_ctrl_v: SingletonCharacterEscape (ControlEsc esc_v) (Character.numeric_value Characters.LINE_TABULATION)
  | Singleton_ctrl_f: SingletonCharacterEscape (ControlEsc esc_f) (Character.numeric_value Characters.FORM_FEED)
  | Singleton_ctrl_r: SingletonCharacterEscape (ControlEsc esc_r) (Character.numeric_value Characters.CARRIAGE_RETURN)
  | Singleton_zero: SingletonCharacterEscape esc_Zero (Character.numeric_value Characters.NULL)
  | Singleton_ascii_control: forall l, SingletonCharacterEscape (AsciiControlEsc l) (NonNegInt.modulo (AsciiLetter.numeric_value l) 32)
  | Singleton_hex: forall d1 d2, SingletonCharacterEscape (HexEscape d1 d2) (HexDigit.to_integer (d1 :: d2 :: nil))
  | Singleton_id: forall c, SingletonCharacterEscape (IdentityEsc c) (Character.numeric_value c)
  | Singleton_unicode_pair: forall d1 d2, SingletonCharacterEscape (UnicodeEsc (Pair d1 d2)) (Unicode.utf16SurrogatePair (HexDigit.to_integer_4 d1) (HexDigit.to_integer_4 d2))
  | Singleton_unicode_lonely: forall d, SingletonCharacterEscape (UnicodeEsc (Lonely d)) (HexDigit.to_integer_4 d)
  | Singleton_unicode_cp: forall c, SingletonCharacterEscape (UnicodeEsc (CodePoint c)) (Character.numeric_value c).

  Inductive SingletonClassAtom: ClassAtom -> non_neg_integer -> Prop :=
  | Singleton_SourceCharacter: forall c, SingletonClassAtom (SourceCharacter c) (Character.numeric_value c)
  | Singleton_b: SingletonClassAtom (ClassEsc esc_b) (Character.numeric_value Characters.BACKSPACE)
  | Singleton_dash: SingletonClassAtom (ClassEsc esc_Dash) (Character.numeric_value Characters.HYPHEN_MINUS)
  | Singleton_char_esc: forall ce c,
      SingletonCharacterEscape ce c -> SingletonClassAtom (ClassEsc (CCharacterEsc ce)) c.

  Inductive Pass_ClassRanges: Patterns.ClassRanges -> Prop :=
  | Pass_EmptyCR: Pass_ClassRanges Patterns.EmptyCR
  | Pass_ClassAtomCR: forall ca t, Pass_ClassRanges t -> Pass_ClassRanges (Patterns.ClassAtomCR ca t)
  | Pass_RangeCR: forall l h cl ch t,
      SingletonClassAtom l cl ->
      SingletonClassAtom h ch ->
      (cl <= ch)%nat ->
      Pass_ClassRanges t ->
      Pass_ClassRanges (Patterns.RangeCR l h t).

  Inductive Pass_CharClass: Patterns.CharClass -> Prop :=
  | Pass_NoninvertedCC: forall crs, Pass_ClassRanges crs -> Pass_CharClass (Patterns.NoninvertedCC crs)
  | Pass_InvertedCC: forall crs, Pass_ClassRanges crs -> Pass_CharClass (Patterns.InvertedCC crs).

  Inductive Pass_AtomEscape: Patterns.AtomEscape -> RegexContext -> Prop :=
  | Pass_DecimalEsc: forall ctx n, (positive_to_non_neg n) <= (countLeftCapturingParensWithin (zip (AtomEsc (DecimalEsc n)) ctx) (nil)) -> Pass_AtomEscape (DecimalEsc n) ctx
  | Pass_CharacterClassEsc: forall ctx esc, Pass_AtomEscape (ACharacterClassEsc esc) ctx
  | Pass_CharacterEsc: forall ctx esc, Pass_AtomEscape (ACharacterEsc esc) ctx
  | Pass_GroupEsc: forall ctx gn, List.length (groupSpecifiersThatMatch (AtomEsc (GroupEsc gn)) ctx gn) = 1 -> Pass_AtomEscape (GroupEsc gn) ctx.

  Inductive Pass_QuantifierPrefix: Patterns.QuantifierPrefix -> Prop :=
  | Pass_Star: Pass_QuantifierPrefix Patterns.Star
  | Pass_Plus: Pass_QuantifierPrefix Patterns.Plus
  | Pass_Question: Pass_QuantifierPrefix Patterns.Question
  | Pass_RepExact: forall n, Pass_QuantifierPrefix (Patterns.RepExact n)
  | Pass_RepPartialRange: forall n, Pass_QuantifierPrefix (Patterns.RepPartialRange n)
  | Pass_RepRange: forall min max, (min <= max)%nat -> Pass_QuantifierPrefix (Patterns.RepRange min max).

  Inductive Pass_Quantifier: Patterns.Quantifier -> Prop :=
  | Pass_Greedy: forall p, Pass_QuantifierPrefix p -> Pass_Quantifier (Patterns.Greedy p)
  | Pass_Lazy: forall p, Pass_QuantifierPrefix p -> Pass_Quantifier (Patterns.Lazy p).

  Inductive Pass_Regex: Patterns.Regex -> RegexContext -> Prop :=
  | Pass_Empty: forall ctx, Pass_Regex Patterns.Empty ctx
  | Pass_Char: forall chr ctx, Pass_Regex (Patterns.Char chr) ctx
  | Pass_Dot: forall ctx, Pass_Regex Patterns.Dot ctx
  | Pass_AtomEsc: forall esc ctx, Pass_AtomEscape esc ctx -> Pass_Regex (Patterns.AtomEsc esc) ctx
  | Pass_CharacterClass: forall cc ctx, Pass_CharClass cc -> Pass_Regex (Patterns.CharacterClass cc) ctx
  | Pass_Disjunction: forall r1 r2 ctx, Pass_Regex r1 (Disjunction_left r2 :: ctx) -> Pass_Regex r2 (Disjunction_right r1 :: ctx) -> Pass_Regex (Patterns.Disjunction r1 r2) ctx
  | Pass_Quantified: forall r q ctx, Pass_Regex r (Quantified_inner q :: ctx) -> Pass_Quantifier q -> Pass_Regex (Patterns.Quantified r q) ctx
  | Pass_Seq: forall r1 r2 ctx, Pass_Regex r1 (Seq_left r2 :: ctx) -> Pass_Regex r2 (Seq_right r1 :: ctx) -> Pass_Regex (Patterns.Seq r1 r2) ctx
  | Pass_Group: forall name r ctx, Pass_Regex r (Group_inner name :: ctx) -> Pass_Regex (Patterns.Group name r) ctx
  | Pass_InputStart: forall ctx, Pass_Regex Patterns.InputStart ctx
  | Pass_InputEnd: forall ctx, Pass_Regex Patterns.InputEnd ctx
  | Pass_WordBoundary: forall ctx, Pass_Regex Patterns.WordBoundary ctx
  | Pass_NotWordBoundary: forall ctx, Pass_Regex Patterns.NotWordBoundary ctx
  | Pass_Lookahead: forall r ctx, Pass_Regex r (Lookahead_inner :: ctx) -> Pass_Regex (Patterns.Lookahead r) ctx
  | Pass_NegativeLookahead: forall r ctx, Pass_Regex r (NegativeLookahead_inner :: ctx) -> Pass_Regex (Patterns.NegativeLookahead r) ctx
  | Pass_Lookbehind: forall r ctx, Pass_Regex r (Lookbehind_inner :: ctx) -> Pass_Regex (Patterns.Lookbehind r) ctx
  | Pass_NegativeLookbehind: forall r ctx, Pass_Regex r (NegativeLookbehind_inner :: ctx) -> Pass_Regex (Patterns.NegativeLookbehind r) ctx.

  Lemma countLeftCapturingParensBefore_contextualized: forall ctx f r,
    Root r (f, ctx) ->
    Pass_Regex r nil ->
    (countLeftCapturingParensBefore f ctx) + (countLeftCapturingParensWithin f ctx) <= countLeftCapturingParensWithin r nil.
  Proof.
    unfold Root; cbn.
    induction ctx; intros f r R_r EEP_r.
    - rewrite -> Zipper.Zip.id in R_r. subst. cbn. lia.
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
      List.Indexing.Nat.indexing (Zipper.Walk.walk (zip r ctx) nil) (f i) = Success (Group (Some gn) r', ctx'')).
  Proof.
    unfold groupSpecifiersThatMatch.
    intros r ctx gn. generalize dependent (Zipper.Walk.walk (zip r ctx) nil). clear r. clear ctx.
    induction l as [| [rh ctxh] l' (f' & H0 & H1) ].
    - exists (fun x => x). split.
      + intros i j <-. reflexivity.
      + intros i r' ctx' Eq_indexed. cbn in Eq_indexed. rewrite -> List.Indexing.Nat.nil in Eq_indexed. Result.assertion_failed_helper.
    - let direct_recursion := solve [ exists (fun i => S (f' i)); setoid_rewrite -> Nat.succ_inj_wd; split; try assumption ] in
        destruct rh; try direct_recursion;
        destruct name as [ name | ]; try direct_recursion;
        cbn; destruct (GroupName_eq_dec name (capturingGroupName gn)) eqn:Eq_gs_gn; try direct_recursion.
      exists (fun i => if Nat.eqb i 0 then 0 else S (f' (i - 1))).
      split.
      + intros i j H. destruct (Nat.eqb i 0) eqn:Eq_i; destruct (Nat.eqb j 0) eqn:Eq_j; spec_reflector Nat.eqb_spec; subst.
        * reflexivity. * discriminate. * discriminate. * apply Nat.succ_inj in H. specialize H0 with (1 := H). lia.
      + intros [| i] r' ctx'; cbn.
        * cbn. subst. subst. intros [=<-<-]. exists ctxh. split; reflexivity.
        * rewrite -> List.Indexing.Nat.cons. rewrite -> Nat.sub_0_r. apply H1.
  Qed.

  Lemma groupSpecifiersThatMatch_too_big_cause {F: Type} {_: Result.AssertionError F}: forall r ctx gn,
    (List.length (groupSpecifiersThatMatch r ctx gn) >= 2)%nat ->
    exists i j ri ctxi rj ctxj,
      i <> j /\
      List.Indexing.Nat.indexing (Zipper.Walk.walk (zip r ctx) nil) i = Success (Group (Some gn) ri, ctxi) /\
      List.Indexing.Nat.indexing (Zipper.Walk.walk (zip r ctx) nil) j = Success (Group (Some gn) rj, ctxj).
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
    generalize dependent (Zipper.Walk.walk (zip r0 ctx0) nil). clear r0. clear ctx0.
    induction l as [ | h t' ]; intros H.
    - discriminate.
    - cbn in H. destruct h as [ h_r h_ctx ].
      destruct h_r; try destruct name as [ name | ]; try solve [ cbn in H; apply (IHt' H) ].
      destruct (GroupName_eq_dec name (capturingGroupName gn)).
      + cbn in H. subst. injection H as <-. split.
        * subst. cbn. lia.
        * exists h_ctx. symmetry. assumption.
      + cbn in H. apply (IHt' H).
  Qed.

  Lemma groupSpecifiersThatMatch_singleton {_: Result.AssertionError SyntaxError}: forall r name,
      List.Exists.exist (Zipper.Walk.walk r nil) (fun node0 =>
        List.Exists.exist (Zipper.Walk.walk r nil) (fun node1 =>
          if node0 =?= node1 then Success false
          else
            let (r0, ctx0) := node0 in
            let (r1, ctx1) := node1 in
            match r0, r1 with
            | Group (Some name0) _, Group (Some name1) _ => Success (name0 == name1)
            | _, _ => Success false
            end))
        = @Success _ SyntaxError false ->
      (List.length (groupSpecifiersThatMatch r nil name) <= 1)%nat.
  Proof.
    intros r name Ex.
    destruct (Compare_dec.lt_dec (List.length (groupSpecifiersThatMatch r nil name)) 2) as [ Ineq | Ineq ].
    - lia.
    - apply Compare_dec.not_lt in Ineq. apply groupSpecifiersThatMatch_too_big_cause in Ineq as (i & j & ri & ctxi & rj & ctxj & Ineq_ij & Eq_indexed_i & Eq_indexed_j).
      rewrite -> Zipper.Zip.id in *.
      apply List.Exists.false_to_prop in Ex. specialize (Ex _ _ Eq_indexed_i).
      apply List.Exists.false_to_prop in Ex. specialize (Ex _ _ Eq_indexed_j). cbn beta in Ex.
      focus § _ [] _ § auto destruct in Ex.
      + injection e as <- <-. pose proof Zipper.Walk.uniqueness as Falsum. specialize Falsum with (1 := Eq_indexed_i) (2 := Eq_indexed_j). contradiction.
      + unfold "==" in *. destruct (name =?= name) eqn:Falsum. * discriminate. * contradiction.
  Qed.

  Lemma isCharacterClass_singleton {F: Type} {_: Result.AssertionError F}: forall c, isCharacterClass c = false -> exists v, SingletonClassAtom c v.
  Proof.
    intros [ ]; cbn.
    - eexists; repeat econstructor.
    - destruct esc eqn:Esc; try discriminate; intros _.
      + eexists. econstructor.
      + eexists. econstructor.
      + clear Esc esc. destruct esc0 eqn:Esc.
        1: { destruct esc; eexists; do 3 econstructor. }
        4: { destruct seq; eexists; do 2 econstructor. }
        all: eexists; do 2 econstructor.
  Qed.


(*   Lemma char_fits_32 n :
    NonNegInt.modulo n 32 < Pos.to_nat 65536.
  Proof.
    etransitivity; [ apply Nat.mod_upper_bound | ]; lia.
  Qed.

  Lemma char_fits_hex_2 d1 d2 :
    HexDigit.to_integer (d1 :: d2 :: nil) < Pos.to_nat 65536.
  Proof.
    etransitivity; [ apply HexDigit.upper_bound_2 | ]; lia.
  Qed.

  Lemma char_fits_hex_4 d :
    HexDigit.to_integer_4 d < Pos.to_nat 65536.
  Proof.
    destruct d.
    apply HexDigit.upper_bound_4.
  Qed. *)


  Lemma characterValue_singleton {F: Type} {_: Result.AssertionError F}: forall c v, characterValue c = @Success _ F v <-> SingletonClassAtom c v.
  Proof.
    intros c v; split; intros H;
      repeat (
        subst ||
        autounfold with result_wrappers in * ||
        unfold nat_to_nni in * ||
        (rewrite -> ?Character.numeric_pseudo_bij) || (*,?Character.numeric_pseudo_bij2 in * by first [ apply char_fits_32 || apply char_fits_hex_2 || apply char_fits_hex_4 || lia ]) || *)
        (* rewrite <- ?CodePoint.numeric_value_from_ascii in * || *)
        cbn ||
        match goal with
        | [ c: ClassAtom |- _] => destruct c
        | [ c: ClassEscape |- _] => destruct c
        | [ c: CharacterEscape |- _] => destruct c
        | [ c: CharacterClassEscape |- _] => destruct c
        | [ c: ControlEscape |- _] => destruct c
        | [ c: RegExpUnicodeEscapeSequence |- _] => destruct c
        | [ S: SingletonClassAtom _ _ |- _ ] => dependent destruction S
        | [ S: SingletonCharacterEscape _ _ |- _ ] => dependent destruction S

        | [ H: Success _ = Success _ |- _ ] => injection H as H
        | [ H: Character.numeric_value _ = Character.numeric_value _ |- _ ] => apply Character.numeric_inj in H as <-
        | [ H: _ = Character.numeric_value _ |- _ ] => apply f_equal with (f := Character.from_numeric_value) in H
        | [ H: _ = _ |- _ ] => cbn in H
        end);
      try solve [
        repeat constructor |
        Result.assertion_failed_helper |
        reflexivity ].
  Qed.

  Section Safety.

    Lemma Safety_characterValue: forall ca, isCharacterClass ca = false -> characterValue ca <> Failure SyntaxError.AssertionFailed.
    Proof.
      intros ca H.
      destruct ca; Result.assertion_failed_helper.
      destruct esc; Result.assertion_failed_helper.
      destruct esc; Result.assertion_failed_helper.
      destruct esc; Result.assertion_failed_helper.
      destruct seq; Result.assertion_failed_helper.
    Qed.

    Lemma Safety_class_ranges: forall c, earlyErrors_class_ranges c <> Failure SyntaxError.AssertionFailed.
    Proof.
      induction c; Result.assertion_failed_helper.
      cbn. focus § _ (_ [] _) § auto destruct; subst; focus § _ [] _ § auto destruct in AutoDest_0; try easy;
        repeat lazymatch goal with
        | [ f: SyntaxError |- _ ] => destruct f
        | [ _: context[ if ?b then _ else _ ] |- _ ] => destruct b eqn:?Eq
        | [ H0: isCharacterClass ?c = false, H1: StaticSemantics.characterValue ?c = Failure SyntaxError.AssertionFailed |- _ ] => exfalso; apply (Safety_characterValue _ H0 H1)
        end; boolean_simplifier; try discriminate.
    Qed.

    Definition Safety_char_class: forall cc, earlyErrors_char_class cc <> Failure SyntaxError.AssertionFailed.
    Proof. destruct cc; cbn; apply Safety_class_ranges. Qed.

    Lemma Safety_rec: forall r ctx, earlyErrors_rec r ctx <> Failure SyntaxError.AssertionFailed.
    Proof.
      induction r; intros ctx H; cbn in H; Result.assertion_failed_helper.
      - focus § _ [] _ § auto destruct in H.
      - apply (Safety_char_class _ H).
      - focus § _ [] _ § auto destruct in H; subst. + apply (IHr2 _ H). + destruct f. apply (IHr1 _ AutoDest_).
      - focus § _ [] _ § auto destruct in H. Result.assertion_failed_helper. apply (IHr _ AutoDest_).
      - focus § _ [] _ § auto destruct in H; subst. + apply (IHr2 _ H). + destruct f. apply (IHr1 _ AutoDest_).
      - apply (IHr _ H).
      - apply (IHr _ H).
      - apply (IHr _ H).
      - apply (IHr _ H).
      - apply (IHr _ H).
    Qed.

    Lemma Safety_earlyErrors: forall r, earlyErrors r nil <> Failure SyntaxError.AssertionFailed.
    Proof.
      intros r H. unfold earlyErrors in H. focus § _ [] _ § auto destruct in H.
      - apply (Safety_rec _ _ H).
      - Result.assertion_failed_helper.
        apply List.Exists.failure_kind in AutoDest_ as (_ & ? & _ & H).
        apply List.Exists.failure_kind in H as (_ & ? & _ & H).
        focus § _ [] _ § auto destruct in H.
    Qed.
  End Safety.

  Section Completeness.
    Lemma Completeness_isCharacterClass_false: forall a, isCharacterClass a = false -> exists c, SingletonClassAtom a c.
    Proof.
      intros a Eq. repeat match goal with
        | [ c: ClassAtom |- _] => destruct c
        | [ c: ClassEscape |- _] => destruct c
        | [ c: CharacterEscape |- _] => destruct c
        | [ c: CharacterClassEscape |- _] => destruct c
        | [ c: ControlEscape |- _] => destruct c
        | [ c: RegExpUnicodeEscapeSequence |- _ ] => destruct c
        end; cbn in Eq; try solve [ discriminate | eexists; repeat econstructor ].
    Qed.

    Lemma Completeness_class_ranges: forall c,
      earlyErrors_class_ranges c = Success false ->
      Pass_ClassRanges c.
    Proof.
      induction c; intros H; cbn in *.
      - constructor.
      - constructor. apply IHc. apply H.
      - focus § _ [] _ § auto destruct in H. boolean_simplifier. focus § _ [] _ § auto destruct in AutoDest_0. subst. injection AutoDest_0 as ?.
        apply Completeness_isCharacterClass_false in H0 as (cl & ?). apply Completeness_isCharacterClass_false in H1 as (ch & ?).
        apply Pass_RangeCR with (cl := cl) (ch := ch); try assumption.
        + destruct s1;
            repeat match goal with
            | [ H: SingletonClassAtom ?c ?cc, G: StaticSemantics.characterValue ?c = _ |- _ ] => rewrite <- (@characterValue_singleton) in H; rewrite -> H in *; injection G as ->
            end; try spec_reflector Nat.leb_spec0; try lia.
        + apply IHc. apply H.
    Qed.

    Definition Completeness_char_class: forall cc, earlyErrors_char_class cc = Success false -> Pass_CharClass cc.
    Proof. intros; destruct cc; constructor; apply Completeness_class_ranges; assumption. Qed.

    Definition Completeness_quantifier_prefix: forall q, earlyErrors_quantifier_prefix q = false -> Pass_QuantifierPrefix q.
    Proof. intros; destruct q; constructor. cbn in H. destruct min as [ ] eqn:Eq_min. - lia. - destruct (max <=? n) eqn:Ineq; spec_reflector Nat.leb_spec0; lia. Qed.


    Definition Completeness_quantifier: forall q, earlyErrors_quantifier q = false -> Pass_Quantifier q.
    Proof. intros; destruct q; constructor; apply Completeness_quantifier_prefix; assumption. Qed.

    Lemma rec: forall root r ctx,
        List.Exists.exist (Zipper.Walk.walk root nil) (fun node0 =>
          List.Exists.exist (Zipper.Walk.walk root nil) (fun node1 =>
            if node0 =?= node1 then Success false
            else
              let (r0, ctx0) := node0 in
              let (r1, ctx1) := node1 in
              match r0, r1 with
              | Group (Some name0) _, Group (Some name1) _ => Success (name0 == name1)
              | _, _ => Success false
              end))
          = @Success _ SyntaxError false ->
      Root root (r, ctx) ->
      earlyErrors_rec r ctx = Success false ->
      Pass_Regex r ctx.
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
          rewrite -> Zipper.Zip.id in *.
          lia.
      - constructor. apply Completeness_char_class. apply EE_r.
      - constructor.
        + cbn in EE_r. focus § _ [] _ § auto destruct in EE_r. apply IHr1; try assumption.
        + cbn in EE_r. focus § _ [] _ § auto destruct in EE_r. apply IHr2; try assumption.
      - constructor. cbn in EE_r. focus § _ [] _ § auto destruct in EE_r. apply IHr; try assumption.
        apply Completeness_quantifier.
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

    Lemma earlyErrors: forall r, earlyErrors r nil = Success false -> Pass_Regex r nil.
    Proof.
      intros r H. unfold earlyErrors in H. focus § _ [] _ § auto destruct in H. apply rec with (root := r); solve [ assumption | reflexivity ].
    Qed.
  End Completeness.
End EarlyErrors.
