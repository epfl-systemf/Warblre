From Coq Require Import PeanoNat ZArith Bool Lia Program.Equality List.
From Warblre Require Import List Tactics Specialize Focus Result Base Patterns StaticSemantics Notation Semantics Definitions.

Import Result.Notations.
Import Semantics.

Module Compile.

  Inductive SingletonClassAtom: ClassAtom -> Character -> Prop :=
  | Singleton_SourceCharacter: forall c, SingletonClassAtom (SourceCharacter c) c.

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
    | NegativeLookbehind: forall r, Regex r -> Regex (Patterns.NegativeLookbehind r)
    | BackReference: forall id, Regex (BackReference id).
  End EarlyErrorsFree.

  Module Safety.

    Lemma compileToCharSet_ClassAtom: forall ca rer, compileToCharSet_ClassAtom ca rer <> compile_assertion_failed.
    Proof. intros [ c ] rer. cbn. easy. Qed.

    Lemma compileToCharSet_ClassAtom_singleton: forall a rer r c,
      SingletonClassAtom a c ->
      Semantics.compileToCharSet_ClassAtom a rer = Success r ->
      r = c :: nil.
    Proof.
      induction a; intros rer c r Sing_a Eq_r; dependent destruction Sing_a.
      cbn in Eq_r. injection Eq_r as <-. reflexivity.
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