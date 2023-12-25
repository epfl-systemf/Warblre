From Coq Require Import List Lia Program.Equality.
From Warblre Require Import List Result Base Patterns StaticSemantics.

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
    | Lookahead: forall r ctx, Regex r (Lookahead_inner :: ctx) -> Regex (Patterns.Lookahead r) ctx
    | NegativeLookahead: forall r ctx, Regex r (NegativeLookahead_inner :: ctx) -> Regex (Patterns.NegativeLookahead r) ctx
    | Lookbehind: forall r ctx, Regex r (Lookbehind_inner :: ctx) -> Regex (Patterns.Lookbehind r) ctx
    | NegativeLookbehind: forall r ctx, Regex r (NegativeLookbehind_inner :: ctx) -> Regex (Patterns.NegativeLookbehind r) ctx.
  End Pass.

  Lemma down: forall ctx root r,
    Root root r ctx ->
    Pass.Regex root nil ->
    Pass.Regex r ctx.
  Proof.
    induction ctx; intros root r R_root P_root.
    - apply Root.nil in R_root. subst. assumption.
    - unfold Root in R_root. destruct a; cbn in R_root; specialize (IHctx _ _ R_root P_root); dependent destruction IHctx; assumption.
  Qed.

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

  Lemma groupSpecifiersThatMatch_is_filter_map: forall r ctx gn i r' ctx',
    List.Indexing.Nat.indexing (groupSpecifiersThatMatch r ctx gn) i = Success (r', ctx') ->
    exists j ctx'',
      Group_inner (Some gn) :: ctx'' = ctx' /\
      List.Indexing.Nat.indexing (pre_order_walk (zip r ctx) nil) j = Success (Group (Some gn) r', ctx'').
  Proof.
    unfold groupSpecifiersThatMatch.
    intros r ctx. generalize dependent (pre_order_walk (zip r ctx) nil). clear r. clear ctx.
    induction l; intros gn i r' ctx' H; cbn in H.
    - rewrite -> List.Indexing.Nat.nil in H. Result.assertion_failed_helper.
    - destruct a as [[ ] ? ]; cbn in H;
        try solve [ specialize IHl with (1 := H) as [ j Eq_indexed ]; exists (S j); rewrite -> List.Indexing.Nat.cons; assumption ].
      destruct name;
        try solve [ specialize IHl with (1 := H) as [ j Eq_indexed ]; exists (S j); rewrite -> List.Indexing.Nat.cons; assumption ].
      destruct (GroupName.eqs t (capturingGroupName gn));
        try solve [ specialize IHl with (1 := H) as [ j Eq_indexed ]; exists (S j); rewrite -> List.Indexing.Nat.cons; assumption ].
      destruct i; cbn in H.
      + subst. injection H as <- <-.
        exists 0. exists l0. cbn. split; reflexivity.
      + specialize IHl with (1 := H) as [ j Eq_indexed ]; exists (S j); rewrite -> List.Indexing.Nat.cons; assumption.
  Qed.

  Lemma groupSpecifiersThatMatch_head_is_group: forall r0 ctx0 gn r ctx t, groupSpecifiersThatMatch r0 ctx0 gn = (r, ctx) :: t ->
    0 < countLeftCapturingParensBefore r ctx /\
    exists ctx', ctx = Group_inner (Some gn) :: ctx'.
  Proof.
    intros r0 ctx0 gn r ctx t H.
    unfold groupSpecifiersThatMatch in H.
    generalize dependent (pre_order_walk (zip r0 ctx0) nil). clear r0. clear ctx0.
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
End EarlyErrors.