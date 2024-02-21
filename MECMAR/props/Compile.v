From Coq Require Import PeanoNat ZArith Bool Lia Program.Equality List.
From Warblre Require Import List Tactics Specialize Focus Result Base Patterns StaticSemantics Notation Semantics Definitions EarlyErrors.

Import Result.Notations.
Import Semantics.

Module Compile.
  Module Safety.

(*     Lemma canonicalize {F: Type} {_: Result.AssertionError F}: forall c rer f, canonicalize rer c <> Failure f.
    Proof.
      intros c rer f. unfold canonicalize. clear_result. focus § _ (_ [] _) § auto destruct.
      apply List.Unique.failure_bounds in AutoDest_2. boolean_simplifier. spec_reflector Nat.eqb_spec.
      contradiction.
    Qed. *)

    Lemma wordCharacters {F: Type} {_: Result.AssertionError F}: forall rer f, wordCharacters rer <> Failure f.
    Proof.
      intros rer f. unfold wordCharacters. clear_result. focus § _ (_ [] _) § auto destruct.
(*       unfold CharSet.filter in *. apply List.Filter.failure_kind in AutoDest_ as [ i [ v [ Eq_indexed Eq_f ]]].
      destruct (Semantics.canonicalize rer v) eqn:Eq_canon.
      - discriminate.
      - injection Eq_f as ->. exfalso. apply (canonicalize _ _ _ Eq_canon). *)
    Qed.

    (* TODO: remove it going with unfolded implementation *)
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
(*       - cbn. apply wordCharacters.
      - cbn. destruct (Semantics.wordCharacters rer) eqn:Eq_wc.
        + easy.
        + exfalso. apply (wordCharacters _ _ Eq_wc). *)
    Qed.

    Lemma compileToCharSet_ClassAtom_singleton: forall a rer r c,
      EarlyErrors.SingletonClassAtom a c ->
      Semantics.compileToCharSet_ClassAtom a rer = Success r ->
      r = CharSet.singleton c.
    Proof.
      induction a; intros rer c r Sing_a Eq_r; dependent destruction Sing_a; cbn in Eq_r; try rewrite -> Character.numeric_pseudo_bij in Eq_r;
        try injection Eq_r as <-; try reflexivity.
      - focus § _ [] _ § auto destruct in Eq_r.
        focus § _ [] _ § auto destruct in AutoDest_; injection AutoDest_ as <-;
          (rewrite -> ?Character.numeric_pseudo_bij in Eq_r; rewrite <- ?CodePoint.numeric_value_from_ascii in Eq_r; subst; dependent destruction H; injection Eq_r as <-; reflexivity).
    Qed.

    Lemma compileToCharSet: forall crs rer,
      EarlyErrors.ClassRanges crs ->
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
          cbn in AutoDest_2. focus § _ [] _ § auto destruct in AutoDest_2.
          boolean_simplifier. spec_reflector Nat.leb_spec0.
          easy.
        + exfalso. apply (IHcrs _ ltac:(eassumption)).
        + exfalso. apply (compileToCharSet_ClassAtom _ _ ltac:(eassumption)).
        + exfalso. apply (compileToCharSet_ClassAtom _ _ ltac:(eassumption)).
    Qed.

    Lemma compileCharacterClass: forall cc rer,
      EarlyErrors.Pass.CharClass cc ->
      compileCharacterClass cc rer <> compile_assertion_failed.
    Proof.
      intros [ crs | crs ] rer H; dependent destruction H.
      - cbn. focus § _ (_ [] _) § auto destruct; destruct f; try easy. exfalso. apply (compileToCharSet _ _ H ltac:(eassumption)).
      - cbn. focus § _ (_ [] _) § auto destruct; destruct f; try easy. exfalso. apply (compileToCharSet _ _ H ltac:(eassumption)).
    Qed.

    Lemma compileSubPattern: forall r ctx rer dir,
      countLeftCapturingParensWithin (zip r ctx) nil = RegExp.capturingGroupsCount rer ->
      EarlyErrors.Pass.Regex r ctx ->
      compileSubPattern r ctx rer dir <> compile_assertion_failed.
    Proof.
      induction r; intros ctx rer dir H EE_r; dependent destruction EE_r; cbn; try discriminate.
      - focus § _ (_ [] _) § auto destruct; dependent destruction H0.
        + boolean_simplifier. spec_reflector Nat.leb_spec0. cbn in *. rewrite -> H in *. contradiction.
        + repeat match goal with | [ H: _ = Failure _ |- _ ] => focus § _ [] _ § auto destruct in H; try injection H as -> end.
        + repeat match goal with | [ H: _ = Failure _ |- _ ] => focus § _ [] _ § auto destruct in H; try injection H as -> end.
        + boolean_simplifier. spec_reflector Nat.eqb_spec. contradiction.
        + destruct (groupSpecifiersThatMatch (AtomEsc (AtomEscape.GroupEsc id)) ctx id) eqn:Eq_gstm; try discriminate.
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
      countLeftCapturingParensWithin r nil = RegExp.capturingGroupsCount rer ->
      EarlyErrors.Pass.Regex r nil ->
      compilePattern r rer <> compile_assertion_failed.
    Proof.
      intros r rer H0 H1. unfold compilePattern. focus § _ (_ [] _) § auto destruct; destruct f; try easy.
      rewrite <- (Zip.id r) in H0.
      exfalso. apply (compileSubPattern _ _ _ _ H0 H1 AutoDest_).
    Qed.
  End Safety.
End Compile.