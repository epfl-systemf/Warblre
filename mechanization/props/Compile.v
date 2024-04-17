From Coq Require Import PeanoNat ZArith Bool Lia Program.Equality List.
From Warblre Require Import List Tactics Specialize Focus Result Base Patterns Node StaticSemantics Notation Semantics Definitions EarlyErrors RegExpRecord.

Import Result.Notations.
Import Semantics.

Section Compile.
  Context {Σ} `{ep: CharacterInstance Σ}.
    Import Patterns.

    Lemma wordCharacters {F: Type} {_: Result.AssertionError F}: forall rer f, wordCharacters rer <> Failure f.
    Proof.
      intros rer f. unfold wordCharacters. clear_result. focus § _ (_ [] _) § auto destruct.
    Qed.

    Lemma compileToCharSet_ClassAtom_rel_ind: forall (P: ClassAtom -> Prop),
      (forall chr, P (SourceCharacter chr)) ->
      P (ClassEsc (esc_b)) ->
      P (ClassEsc (esc_Dash)) ->
      (forall esc, P (ClassEsc (CCharacterEsc esc))) ->
      P (ClassEsc (CCharacterClassEsc esc_d)) ->
      P (ClassEsc (CCharacterClassEsc esc_s)) ->
      P (ClassEsc (CCharacterClassEsc esc_w)) ->
      (forall p, P (ClassEsc (CCharacterClassEsc (UnicodeProp p)))) ->
      (P (ClassEsc (CCharacterClassEsc esc_d)) -> P (ClassEsc (CCharacterClassEsc esc_D)) ) ->
      (P (ClassEsc (CCharacterClassEsc esc_s)) -> P (ClassEsc (CCharacterClassEsc esc_S)) ) ->
      (P (ClassEsc (CCharacterClassEsc esc_w)) -> P (ClassEsc (CCharacterClassEsc esc_W)) ) ->
      (forall p, P (ClassEsc (CCharacterClassEsc (UnicodeProp p))) -> P (ClassEsc (CCharacterClassEsc (UnicodePropNeg p))) ) ->
      forall ca, P ca.
    Proof.
      intros P H_char H_b H_dash H_char_esc H_d H_s H_w H_D H_S H_W.
      destruct ca; auto.
      destruct esc; auto.
      destruct esc; auto.
    Qed.

    Lemma compileToCharSet_ClassAtom: forall ca rer, compileToCharSet_ClassAtom ca rer <> compile_assertion_failed.
    Proof.
      induction ca using compileToCharSet_ClassAtom_rel_ind; intros rer; try easy.
      destruct esc; try easy.
      - destruct esc; try easy.
      - destruct seq; try easy.
    Qed.

    Lemma compileToCharSet_ClassAtom_singleton: forall a rer r i,
      EarlyErrors.SingletonClassAtom a i ->
      Semantics.compileToCharSet_ClassAtom a rer = Success r ->
      r = CharSet.singleton (Character.from_numeric_value i).
    Proof.
      induction a; intros rer c r Sing_a Eq_r; dependent destruction Sing_a; cbn in Eq_r.
      - injection Eq_r as <-. rewrite -> Character.numeric_pseudo_bij. reflexivity.
      - unfold nat_to_nni in Eq_r; cbn in Eq_r. rewrite -> Character.numeric_pseudo_bij in Eq_r; injection Eq_r as <-.
        rewrite -> Character.numeric_pseudo_bij. reflexivity.
      - unfold nat_to_nni in Eq_r; cbn in Eq_r. rewrite -> Character.numeric_pseudo_bij in Eq_r; injection Eq_r as <-.
        rewrite -> Character.numeric_pseudo_bij. reflexivity.
      - destruct ce; try destruct esc; dependent destruction H.
        all: unfold nat_to_nni in Eq_r; cbn in Eq_r; unfold characterValue_Hex4Digits in Eq_r. 
        all: try rewrite -> Character.numeric_pseudo_bij in Eq_r; injection Eq_r as <-.
        all: try rewrite -> Character.numeric_pseudo_bij; try reflexivity.
    Qed.

    Lemma compileToCharSet: forall crs rer,
      EarlyErrors.Pass_ClassRanges crs ->
      compileToCharSet crs rer <> compile_assertion_failed.
    Proof.
      induction crs; intros rer H; dependent destruction H; cbn.
      - easy.
      - specialize IHcrs with (1 := H).
        focus § _ (_ [] _) § auto destruct; destruct f; try easy.
        + congruence.
        + exfalso. apply (compileToCharSet_ClassAtom _ _ ltac:(eassumption)).
      - specialize IHcrs with (1 := H2).
        focus § _ (_ [] _) § auto destruct; destruct f; try easy.
        + pose proof (compileToCharSet_ClassAtom_singleton _ _ _ _ H ltac:(eassumption)) as ->.
          pose proof (compileToCharSet_ClassAtom_singleton _ _ _ _ H0 ltac:(eassumption)) as ->.
          unfold characterRange in *. repeat rewrite -> CharSet.singleton_size,CharSet.singleton_unique in *.
          cbn in AutoDest_2. focus § _ [] _ § auto destruct in AutoDest_2.
          boolean_simplifier. spec_reflector Nat.leb_spec0.
          apply Character.numeric_round_trip_order in H1.
          contradiction.
        + exfalso. apply (IHcrs _ ltac:(eassumption)).
        + exfalso. apply (compileToCharSet_ClassAtom _ _ ltac:(eassumption)).
        + exfalso. apply (compileToCharSet_ClassAtom _ _ ltac:(eassumption)).
    Qed.

    Lemma compileCharacterClass: forall cc rer,
      EarlyErrors.Pass_CharClass cc ->
      compileCharacterClass cc rer <> compile_assertion_failed.
    Proof.
      intros [ crs | crs ] rer H; dependent destruction H.
      - cbn. focus § _ (_ [] _) § auto destruct; destruct f; try easy. exfalso. apply (compileToCharSet _ _ H ltac:(eassumption)).
      - cbn. focus § _ (_ [] _) § auto destruct; destruct f; try easy. exfalso. apply (compileToCharSet _ _ H ltac:(eassumption)).
    Qed.

    Lemma compileSubPattern: forall r ctx rer dir,
      countLeftCapturingParensWithin (zip r ctx) nil = RegExpRecord.capturingGroupsCount rer ->
      EarlyErrors.Pass_Regex r ctx ->
      compileSubPattern r ctx rer dir <> compile_assertion_failed.
    Proof.
      induction r; intros ctx rer dir H EE_r; dependent destruction EE_r; cbn; try discriminate.
      - focus § _ (_ [] _) § auto destruct; dependent destruction H0.
        + boolean_simplifier. spec_reflector Nat.leb_spec0. cbn in *. rewrite -> H in *. contradiction.
        + repeat match goal with | [ H: _ = Failure _ |- _ ] => focus § _ [] _ § auto destruct in H; try injection H as -> end.
        + repeat match goal with | [ H: _ = Failure _ |- _ ] => focus § _ [] _ § auto destruct in H; try injection H as -> end.
        + boolean_simplifier. spec_reflector Nat.eqb_spec. contradiction.
        + destruct (groupSpecifiersThatMatch (AtomEsc (GroupEsc id)) ctx id) eqn:Eq_gstm; try discriminate.
          destruct p. apply EarlyErrors.groupSpecifiersThatMatch_head_is_group in Eq_gstm as [ ? [ ? -> ] ].
          apply NonNegInt.failure in AutoDest_2.
          apply List.Unique.head in AutoDest_1. subst. cbn in *. lia.
        + boolean_simplifier. spec_reflector Nat.eqb_spec.
          apply List.Unique.failure_bounds in AutoDest_1. contradiction.
      - focus § _ (_ [] _) § auto destruct; destruct f; try easy.
        exfalso. apply (compileCharacterClass _ _ H0 ltac:(eassumption)).
      - focus § _ (_ [] _) § auto destruct; destruct f; try easy.
        + exfalso. apply IHr2 with (3 := ltac:(eassumption)); assumption.
        + exfalso. apply IHr1 with (3 := ltac:(eassumption)); assumption.
      - focus § _ (_ [] _) § auto destruct. destruct f; try easy.
        exfalso. apply IHr with (3 := ltac:(eassumption)); assumption.
      - focus § _ (_ [] _) § auto destruct; destruct f; try easy.
        + exfalso. apply IHr2 with (3 := ltac:(eassumption)); assumption.
        + exfalso. apply IHr1 with (3 := ltac:(eassumption)); assumption.
      - focus § _ (_ [] _) § auto destruct; destruct f; try easy.
        exfalso. apply IHr with (3 := ltac:(eassumption)); assumption.
      - focus § _ (_ [] _) § auto destruct; destruct f; try easy.
        exfalso. apply IHr with (3 := ltac:(eassumption)); assumption.
      - focus § _ (_ [] _) § auto destruct; destruct f; try easy.
        exfalso. apply IHr with (3 := ltac:(eassumption)); assumption.
      - focus § _ (_ [] _) § auto destruct; destruct f; try easy.
        exfalso. apply IHr with (3 := ltac:(eassumption)); assumption.
      - focus § _ (_ [] _) § auto destruct; destruct f; try easy.
        exfalso. apply IHr with (3 := ltac:(eassumption)); assumption.
    Qed.

    Lemma compilePattern: forall r rer,
      countLeftCapturingParensWithin r nil = RegExpRecord.capturingGroupsCount rer ->
      EarlyErrors.Pass_Regex r nil ->
      compilePattern r rer <> compile_assertion_failed.
    Proof.
      intros r rer H0 H1. unfold compilePattern. focus § _ (_ [] _) § auto destruct; destruct f; try easy.
      rewrite <- (Zipper.Zip.id r) in H0.
      exfalso. apply (compileSubPattern _ _ _ _ H0 H1 AutoDest_).
    Qed.

    Theorem compilePattern_success: forall r rer,
      countLeftCapturingParensWithin r nil = RegExpRecord.capturingGroupsCount rer ->
      EarlyErrors.Pass_Regex r nil ->
      exists m, Semantics.compilePattern r rer = Success m.
    Proof.
      intros. destruct (Semantics.compilePattern r rer) as [ | [ ] ] eqn:Eq.
      - exists s. reflexivity.
      - pose proof (compilePattern r rer) as Falsum. fforward Falsum. contradiction.
    Qed.
End Compile.