From Coq Require Import PeanoNat ZArith Bool Lia Program.Equality List.
From Warblre Require Import List Tactics Specialize Focus Result Base Patterns StaticSemantics Notation Semantics Definitions.

Import Result.Notations.
Import Semantics.

Module Compile.

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

  Module EarlyErrorsFree.

    Inductive ClassRanges: Patterns.ClassRanges -> Prop :=
    | EmptyCR: ClassRanges Patterns.EmptyCR
    | ClassAtomCR: forall ca t, ClassRanges t -> ClassRanges (Patterns.ClassAtomCR ca t)
    | RangeCR: forall l h cl ch t,
        SingletonClassAtom l cl ->
        SingletonClassAtom h ch ->
        (Character.numeric_value cl <= Character.numeric_value ch)%nat ->
        ClassRanges t ->
        ClassRanges (Patterns.RangeCR l h t).

    Inductive CharClass: Patterns.CharClass -> Prop :=
    | NoninvertedCC: forall crs, ClassRanges crs -> CharClass (Patterns.NoninvertedCC crs)
    | InvertedCC: forall crs, ClassRanges crs -> CharClass (Patterns.InvertedCC crs).

    Inductive Regex: Patterns.Regex -> Prop :=
    | Empty: Regex Patterns.Empty
    | Char: forall chr, Regex (Patterns.Char chr)
    | Dot: Regex Patterns.Dot
    | CharacterClass: forall cc, CharClass cc -> Regex (Patterns.CharacterClass cc)
    | Disjunction: forall r1 r2, Regex r1 -> Regex r2 -> Regex (Patterns.Disjunction r1 r2)
    | Quantified: forall r q, Regex r -> Regex (Patterns.Quantified r q)
    | Seq: forall r1 r2, Regex r1 -> Regex r2 -> Regex (Patterns.Seq r1 r2)
    | Group: forall name r, Regex r -> Regex (Patterns.Group name r)
    | Lookahead: forall r, Regex r -> Regex (Patterns.Lookahead r)
    | NegativeLookahead: forall r, Regex r -> Regex (Patterns.NegativeLookahead r)
    | Lookbehind: forall r, Regex r -> Regex (Patterns.Lookbehind r)
    | NegativeLookbehind: forall r, Regex r -> Regex (Patterns.NegativeLookbehind r).
  End EarlyErrorsFree.

  Module Safety.

    Lemma canonicalize: forall c rer, canonicalize rer c <> compile_assertion_failed.
    Proof.
      intros c rer. unfold canonicalize. focus § _ (_ [] _) § auto destruct.
      apply List.Unique.failure_bounds in AutoDest_2. boolean_simplifier. spec_reflector Nat.eqb_spec.
      contradiction.
    Qed.

    Lemma wordCharacters: forall rer, wordCharacters rer <> compile_assertion_failed.
    Proof.
      intros rer. unfold wordCharacters. focus § _ (_ [] _) § auto destruct.
      unfold CharSet.filter in AutoDest_. apply List.Filter.failure_kind in AutoDest_ as [ i [ v [ Eq_indexed Eq_f ]]].
      destruct (Semantics.canonicalize rer v) eqn:Eq_canon.
      - discriminate.
      - injection Eq_f as ->. exfalso. destruct f. apply (canonicalize _ _ Eq_canon).
    Qed.

    Lemma compileToCharSet_ClassAtom_rel_ind: forall (P: ClassAtom -> Prop),
      (forall chr, P (SourceCharacter chr)) ->
      P (ClassEsc (ClassEscape.b)) ->
      P (ClassEsc (ClassEscape.Dash)) ->
      (forall esc, P (ClassEsc (ClassEscape.CharacterEsc esc))) ->
      P (ClassEsc (ClassEscape.CharacterClassEsc CharacterClassEscape.d)) ->
      P (ClassEsc (ClassEscape.CharacterClassEsc CharacterClassEscape.s)) ->
      P (ClassEsc (ClassEscape.CharacterClassEsc CharacterClassEscape.w)) ->
      (P (ClassEsc (ClassEscape.CharacterClassEsc CharacterClassEscape.d)) -> P (ClassEsc (ClassEscape.CharacterClassEsc CharacterClassEscape.D)) ) ->
      (P (ClassEsc (ClassEscape.CharacterClassEsc CharacterClassEscape.s)) -> P (ClassEsc (ClassEscape.CharacterClassEsc CharacterClassEscape.S)) ) ->
      (P (ClassEsc (ClassEscape.CharacterClassEsc CharacterClassEscape.w)) -> P (ClassEsc (ClassEscape.CharacterClassEsc CharacterClassEscape.W)) ) ->
      forall ca, P ca.
    Proof.
      intros P H_char H_b H_dash H_char_esc H_d H_s H_w H_D H_S H_W.
      destruct ca; auto.
      destruct esc; auto.
      destruct esc; auto.
    Qed.

    Lemma compileToCharSet_ClassAtom: forall ca rer, compileToCharSet_ClassAtom ca rer <> compile_assertion_failed.
    Proof.
      induction ca using compileToCharSet_ClassAtom_rel_ind; intros rer;
        repeat match goal with
        | [ t: ?T |- _ ] => lazymatch T with
            | RegExp => fail
            | Character => fail
            | CharacterClassEscape => fail
            | _ => destruct t
            end
        end; try solve [ cbn; try easy ].
      - cbn. apply wordCharacters.
      - cbn. destruct (Semantics.wordCharacters rer) eqn:Eq_wc.
        + easy.
        + destruct f. exfalso. apply (wordCharacters _ Eq_wc).
    Qed.

    Lemma compileToCharSet_ClassAtom_singleton: forall a rer r c,
      SingletonClassAtom a c ->
      Semantics.compileToCharSet_ClassAtom a rer = Success r ->
      r = c :: nil.
    Proof.
      induction a; intros rer c r Sing_a Eq_r; dependent destruction Sing_a; cbn in Eq_r; try rewrite -> Character.numeric_pseudo_bij in Eq_r;
        try injection Eq_r as <-; try reflexivity.
      - focus § _ [] _ § auto destruct in Eq_r.
        focus § _ [] _ § auto destruct in AutoDest_; injection AutoDest_ as <-;
          rewrite -> Character.numeric_pseudo_bij in Eq_r; subst; dependent destruction H; injection Eq_r as <-; reflexivity.
    Qed.

    Lemma compileToCharSet: forall crs rer,
      EarlyErrorsFree.ClassRanges crs ->
      compileToCharSet crs rer <> compile_assertion_failed.
    Proof.
      induction crs; intros rer H; dependent destruction H; cbn.
      - easy.
      - specialize IHcrs with (1 := H).
        focus § _ (_ [] _) § auto destruct; destruct f; try easy.
        + congruence.
        + exfalso. apply (compileToCharSet_ClassAtom _ _ AutoDest_).
      - specialize IHcrs with (1 := H2).
        focus § _ (_ [] _) § auto destruct; destruct f; try easy.
        + pose proof (compileToCharSet_ClassAtom_singleton _ _ _ _ H AutoDest_) as ->.
          pose proof (compileToCharSet_ClassAtom_singleton _ _ _ _ H0 AutoDest_0) as ->.
          cbn in AutoDest_2. focus § _ [] _ § auto destruct in AutoDest_2.
          boolean_simplifier. spec_reflector Nat.leb_spec0.
          easy.
        + exfalso. apply (IHcrs _ AutoDest_1).
        + exfalso. apply (compileToCharSet_ClassAtom _ _ AutoDest_0).
        + exfalso. apply (compileToCharSet_ClassAtom _ _ AutoDest_).
    Qed.

    Lemma compileCharacterClass: forall cc rer,
      EarlyErrorsFree.CharClass cc ->
      compileCharacterClass cc rer <> compile_assertion_failed.
    Proof.
      intros [ crs | crs ] rer H; dependent destruction H.
      - cbn. focus § _ (_ [] _) § auto destruct; destruct f; try easy. exfalso. apply (compileToCharSet _ _ H AutoDest_).
      - cbn. focus § _ (_ [] _) § auto destruct; destruct f; try easy. exfalso. apply (compileToCharSet _ _ H AutoDest_).
    Qed.

    Lemma compileSubPattern: forall r ctx rer dir,
      EarlyErrorsFree.Regex r ->
      compileSubPattern r ctx rer dir <> compile_assertion_failed.
    Proof.
      induction r; intros ctx rer dir H; dependent destruction H; cbn; try discriminate.
      - focus § _ (_ [] _) § auto destruct; destruct f; try easy.
        exfalso. apply (compileCharacterClass _ _ H AutoDest_).
      - focus § _ (_ [] _) § auto destruct; destruct f; try easy.
        + exfalso. apply IHr2 with (2 := AutoDest_0). assumption.
        + exfalso. apply IHr1 with (2 := AutoDest_). assumption.
      - focus § _ (_ [] _) § auto destruct. destruct f; try easy.
        exfalso. apply IHr with (2 := AutoDest_). assumption.
      - focus § _ (_ [] _) § auto destruct; destruct f; try easy.
        + exfalso. apply IHr2 with (2 := AutoDest_0). assumption.
        + exfalso. apply IHr1 with (2 := AutoDest_). assumption.
      - focus § _ (_ [] _) § auto destruct; destruct f; try easy.
        exfalso. apply IHr with (2 := AutoDest_). assumption.
      - focus § _ (_ [] _) § auto destruct; destruct f; try easy.
        exfalso. apply IHr with (2 := AutoDest_). assumption.
      - focus § _ (_ [] _) § auto destruct; destruct f; try easy.
        exfalso. apply IHr with (2 := AutoDest_). assumption.
      - focus § _ (_ [] _) § auto destruct; destruct f; try easy.
        exfalso. apply IHr with (2 := AutoDest_). assumption.
      - focus § _ (_ [] _) § auto destruct; destruct f; try easy.
        exfalso. apply IHr with (2 := AutoDest_). assumption.
    Qed.

    Lemma compilePattern: forall r rer,
      EarlyErrorsFree.Regex r ->
      compilePattern r rer <> compile_assertion_failed.
    Proof.
      intros r rer H. unfold compilePattern. focus § _ (_ [] _) § auto destruct; destruct f; try easy.
      exfalso. apply (compileSubPattern _ _ _ _ H AutoDest_).
    Qed.
  End Safety.
End Compile.