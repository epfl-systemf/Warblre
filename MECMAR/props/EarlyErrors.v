From Warblre Require Import Base Patterns StaticSemantics.

Module EarlyErrors.

  Inductive SingletonCharacterEscape: CharacterEscape -> Character -> Prop :=
  | Singleton_ctrl_t: SingletonCharacterEscape (CharacterEscape.ControlEsc ControlEscape.t) Characters.CHARACTER_TABULATION
  | Singleton_ctrl_n: SingletonCharacterEscape (CharacterEscape.ControlEsc ControlEscape.n) Characters.LINE_FEED
  | Singleton_ctrl_v: SingletonCharacterEscape (CharacterEscape.ControlEsc ControlEscape.v) Characters.LINE_TABULATION
  | Singleton_ctrl_f: SingletonCharacterEscape (CharacterEscape.ControlEsc ControlEscape.f) Characters.FORM_FEED
  | Singleton_ctrl_r: SingletonCharacterEscape (CharacterEscape.ControlEsc ControlEscape.r) Characters.CARRIAGE_RETURN
  | Singleton_zero: SingletonCharacterEscape CharacterEscape.Zero Characters.NULL
  | Singleton_id: forall c, SingletonCharacterEscape (CharacterEscape.IdentityEsc c) c.

  Inductive SingletonClassAtom: ClassAtom -> Character -> Prop :=
  | Singleton_SourceCharacter: forall c, SingletonClassAtom (SourceCharacter c) c
  | Singleton_b: SingletonClassAtom (ClassEsc ClassEscape.b) Characters.BACKSPACE
  | Singleton_dash: SingletonClassAtom (ClassEsc ClassEscape.Dash) Characters.HYPHEN_MINUS
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

    Inductive AtomEscape: Patterns.AtomEscape -> non_neg_integer -> Prop :=
    | DecimalEsc: forall n m, (proj1_sig n) <= m -> AtomEscape (Patterns.AtomEscape.DecimalEsc n) m
    | CharacterClassEsc: forall esc m, AtomEscape (Patterns.AtomEscape.CharacterClassEsc esc) m
    | CharacterEsc: forall esc m, AtomEscape (Patterns.AtomEscape.CharacterEsc esc) m.

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

    Inductive Regex: Patterns.Regex -> non_neg_integer -> Prop :=
    | Empty: forall m, Regex Patterns.Empty m
    | Char: forall chr m, Regex (Patterns.Char chr) m
    | Dot: forall m, Regex Patterns.Dot m
    | AtomEsc: forall esc m, AtomEscape esc m -> Regex (Patterns.AtomEsc esc) m
    | CharacterClass: forall cc m, CharClass cc -> Regex (Patterns.CharacterClass cc) m
    | Disjunction: forall r1 r2 m, Regex r1 m -> Regex r2 m -> Regex (Patterns.Disjunction r1 r2) m
    | Quantified: forall r q m, Regex r m -> Quantifier q -> Regex (Patterns.Quantified r q) m
    | Seq: forall r1 r2 m, Regex r1 m -> Regex r2 m -> Regex (Patterns.Seq r1 r2) m
    | Group: forall name r m, Regex r m -> Regex (Patterns.Group name r) m
    | Lookahead: forall r m, Regex r m -> Regex (Patterns.Lookahead r) m
    | NegativeLookahead: forall r m, Regex r m -> Regex (Patterns.NegativeLookahead r) m
    | Lookbehind: forall r m, Regex r m -> Regex (Patterns.Lookbehind r) m
    | NegativeLookbehind: forall r m, Regex r m -> Regex (Patterns.NegativeLookbehind r) m.
  End Pass.

  Lemma countLeftCapturingParensBefore_contextualized: forall ctx f r m,
      Root r f ctx ->
      Pass.Regex r m ->
      (countLeftCapturingParensBefore f ctx) + (countLeftCapturingParensWithin f ctx) <= m.
    Proof. Admitted.
      (* unfold Root.
      induction ctx.
      - intros f r n m Eq H. cbn in *. subst. unfold countLeftCapturingParensWithin.
        destruct (existence f) as [ m' H' ].
        apply shift_defs with (s := 1) in H'. cbn in *.
        split.
        + apply swap_refs with (1 := H') (2 := H).
        + pose proof (unique_length_defs _ _ _ _ H) as <-. 
          pose proof (monotony _ _ _ _ H).
          lia.
      - unfold countLeftCapturingParensBefore,countLeftCapturingParensWithin in *.
        intros f r n m Eq H.
        destruct a; cbn in Eq |- *;
          specialize IHctx with (1 := Eq) (2 := H) as [ R B ]; cbn in R,B; dependent destruction R;
          repeat match goal with | [ H: Ranges _ _ ?e _ |- _ ] => is_var e; pose proof (normalize_end_defs _ _ _ _ H) as -> end;
          repeat rewrite -> Nat.add_0_r;
          (* Normalize additions by first pushing + 1 to the right and then normalizing + nesting *)
          repeat rewrite <- (Nat.add_assoc _ 1 _) in *;
          repeat rewrite -> (Nat.add_comm 1 (countLeftCapturingParensWithin_impl _)) in *;
          repeat rewrite -> Nat.add_assoc in *;
          split; try (assumption + lia).
        + rewrite <- Nat.add_1_r in R. apply shift_neg_defs with (s := 1) in R; try lia.
          repeat rewrite -> Nat.add_sub in *.
          apply shift_defs. assumption.
    Qed. *)
End EarlyErrors.