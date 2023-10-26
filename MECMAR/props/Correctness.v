From Coq Require Import PeanoNat ZArith Bool Lia Program.Equality.
From Warblre Require Import Tactics Focus Result Base Patterns StaticSemantics Notation Semantics.

Import Result.Notations.

Module Correctness.
  Import Patterns.
  Import Notation.
  Import Semantics.

  Create HintDb warblre.

  Notation "x '[@' n ']'" := (match_state (MatchState.input x) n (MatchState.captures x)) (at level 50, left associativity).
  Notation "x '[$' c ']'" := (match_state (MatchState.input x) (MatchState.endIndex x) c) (at level 50, left associativity).
  Notation "x '[@' n '$' c ']'" := (match_state (MatchState.input x) n c) (at level 50, left associativity).

  Inductive directionalProgress: direction -> MatchState -> MatchState -> Prop :=
  | dpForward: forall x y, (MatchState.endIndex x <= MatchState.endIndex y)%Z -> directionalProgress forward x y
  | dpBackward: forall x y, (MatchState.endIndex x >= MatchState.endIndex y)%Z -> directionalProgress backward x y
  .
  #[export]
  Hint Constructors directionalProgress : core.

  Inductive progress: direction -> MatchState -> MatchResult -> Prop :=
  | pStep: forall dir x y, 
      (MatchState.input x) = (MatchState.input y)
    -> directionalProgress dir x y
    -> progress dir x (Success y)
  | pFail: forall dir x f, progress dir x (Failure f)
  .
  #[export]
  Hint Constructors progress : core.

  Ltac destruct_dps := repeat lazymatch goal with
  | [ H: directionalProgress ?d _ _ |- _ ] => is_constructor d; inversion H; clear H
  end.

  Ltac saturate_transitive rel trans := repeat match goal with
  | [ R1: rel ?S ?T, R2: rel ?T ?U |- _ ] => lazymatch goal with
    |  [ _ : rel S U |- _ ] => fail
    | [ |- _ ] => pose proof (trans S T U R1 R2)
    end
  end; try assumption.

  Module MatchState.
    Lemma reconstruction: forall x, x = match_state (MatchState.input x) (MatchState.endIndex x) (MatchState.captures x).
    Proof. destruct x. reflexivity. Qed.

    Lemma id: forall x, x [@ MatchState.endIndex x ] = x.
    Proof. intros. destruct x; reflexivity. Qed.

    Lemma normalize: forall x e c, x [$ c] [@ e] = x [@ e] [$ c].
    Proof. intros. destruct x; reflexivity. Qed.
  End MatchState.

  Module Progress.
    Lemma refl: forall dir x, (progress dir) x (Success x).
    Proof. intros. destruct dir; constructor; try reflexivity; constructor; normalize_Z_comp; apply Z.le_refl. Qed.

    Lemma trans: forall dir x y z, (progress dir) x (Success y) -> (progress dir) y z -> (progress dir) x z.
    Proof.
      intros.
      repeat match goal with
      | [ H: (progress _) _ (Success _) |- _ ] => inversion H; clear H; subst

      | [ |- (progress _) _ ?y ] => is_var y; let Eq := fresh "Eq" y in destruct y eqn:Eq
      | [ |- (progress _) _ ?y ] => constructor
      end.
      - congruence.
      - destruct dir; destruct_dps; constructor; normalize_Z_comp; saturate_transitive Z.le Z.le_trans.
    Qed.

    Lemma restate: forall dir x y,
          (progress dir) x (Success y)
      ->  (progress dir) x (Success (x [@ MatchState.endIndex y])).
    Proof.
      intros. inversion H. constructor; simpl in *.
      - reflexivity.
      - destruct dir; destruct_dps; constructor; assumption.
    Qed.

    Lemma ignores_captures: forall dir x y cx cy,
          (progress dir) x (Success y) 
      ->  (progress dir) 
            (match_state (MatchState.input x) (MatchState.endIndex x) cx)
            (Success (match_state (MatchState.input y) (MatchState.endIndex y) cy)).
    Proof.
      intros. inversion H. constructor; simpl.
      - assumption.
      - destruct dir; destruct_dps; constructor; assumption.
    Qed.

    Lemma ignores_captures_r: forall dir x n c,
          (progress dir) x (Success (x [@ n $ c]))
      <->  (progress dir) x (Success (x [@ n])).
    Proof.
      intros; split; intros; inversion H; constructor; simpl.
      - assumption.
      - destruct dir; destruct_dps; constructor; assumption.
      - reflexivity.
      - destruct dir; destruct_dps; constructor; assumption.
    Qed.

    Lemma ignores_captures_l: forall dir x n c,
          (progress dir) (x [@ n $ c]) (Success x)
      <->  (progress dir) (x [@ n]) (Success x).
    Proof.
      intros; split; intros; inversion H; constructor; simpl.
      - assumption.
      - destruct dir; destruct_dps; constructor; assumption.
      - reflexivity.
      - destruct dir; destruct_dps; constructor; assumption.
    Qed.

    Lemma simplify_l: forall dir x y c, progress dir (x [$ c]) (Success y) <-> progress dir x (Success y).
    Proof.
      intros; split; intros; inversion H; constructor; simpl.
      - assumption.
      - destruct dir; destruct_dps; constructor; assumption.
      - assumption.
      - destruct dir; destruct_dps; constructor; assumption.
    Qed.

    Lemma simplify_r: forall dir x y c, progress dir x (Success (y [$ c])) <-> progress dir x (Success y).
    Proof.
      intros; split; intros; inversion H; constructor; simpl.
      - assumption.
      - destruct dir; destruct_dps; constructor; assumption.
      - assumption.
      - destruct dir; destruct_dps; constructor; assumption.
    Qed.
    
    Lemma normalize: forall dir x y, progress dir x (Success y) -> y = (x [@ MatchState.endIndex y] [$ MatchState.captures y]).
    Proof. intros. inversion H. destruct y. cbn in *. subst. reflexivity. Qed.

    Ltac clean := repeat
    (   rewrite -> MatchState.id in *
    ||  rewrite -> MatchState.normalize in *
    ||  rewrite -> Progress.ignores_captures_r in *
    ||  rewrite -> Progress.simplify_l in *
    ||  rewrite -> Progress.simplify_r in *
    ||  lazymatch goal with
        | [ H: progress _ ?x (Success (?x [@ _ ] [$ _ ])) |- _ ] => fail
        | [ H: progress _ ?x (Success ?y) |- _ ] =>
          let Eq := fresh "Eq" x y in
          pose proof normalize _ _ _ H as Eq;
          rewrite -> Eq in *
        end
    ||  assumption).
  End Progress.

  Ltac ignore_captures_change' x captures :=
    apply Progress.trans with (y := (match_state (MatchState.input x) (MatchState.endIndex x) captures));
    [ replace x with (match_state (MatchState.input x) (MatchState.endIndex x) (MatchState.captures x)) at 1 by (destruct x; reflexivity);
      apply Progress.ignores_captures; apply Progress.refl
    | idtac ].
  Ltac ignore_captures_change := match goal with
  | [ |- progress _ ?x (_ (match_state (MatchState.input ?x) (MatchState.endIndex ?x) ?captures)) ] => is_var x; ignore_captures_change' x captures
  | [ |- progress _ ?x (_ (match_state (MatchState.input ?x) (MatchState.endIndex ?x) ?captures) _) ] => is_var x; ignore_captures_change' x captures
  end.

  Definition OnInput (x: MatchState) (str: list Character) := MatchState.input x = str.
  Definition MonotonousContinuation (dir: direction) (str: list Character) (c: MatcherContinuation) := forall x, OnInput x str -> (progress dir) x (c x).
  Definition MonotonousMatcher (dir: direction) (str: list Character) (m: Matcher) := forall x c, OnInput x str -> (MonotonousContinuation dir str) c -> (progress dir) x (m x c).
  #[export]
  Hint Transparent MonotonousContinuation MonotonousMatcher : core.

  Module Monotony.
    Lemma matcher_to_continuation: forall dir str m c, MonotonousMatcher dir str m -> MonotonousContinuation dir str c 
      -> MonotonousContinuation dir str (fun (x: MatchState) => m x c).
    Proof. intros. unfold MonotonousContinuation. intros. apply H; assumption. Qed.

    Lemma repeatMatcher: forall fuel dir str x m min max greedy c groupsWithin,
              MonotonousMatcher dir str m
          ->  MonotonousContinuation dir str c
          ->  OnInput x str
          ->  progress dir x (repeatMatcher' m min max greedy x c groupsWithin fuel).
    Proof.
      induction fuel; intros; delta repeatMatcher'; try constructor.
      cbn.
      repeat match goal with
      | [ |- (progress _) _ (if ?b then _ else _) ] => destruct b
      end; try solve
      [ apply H0; assumption
      | ignore_captures_change; apply H;
        [ assumption
        | delta MonotonousContinuation; cbn; intros;
          repeat match goal with
          | [ |- (progress _) _ (if ?b then _ else _) ] => destruct b
          end; try (now constructor);
          apply IHfuel with (str := str); assumption ] ].
    Qed.

    Lemma compileSubpattern: forall r rer dir str, MonotonousMatcher dir str (compileSubPattern r rer dir).
    Proof.
      induction r.
      - delta MonotonousMatcher. cbn. intros.
        repeat match goal with
        | [ |- (progress _) _ (if ?b then _ else _) ] => destruct b
        | [ |- (progress _) _ (match ?b with | _ => _ end) ] => destruct b
        end; try now constructor.
        destruct dir;
          (lazymatch goal with [ |- progress _ _ (_ ?x') ] => apply Progress.trans with (y := x') end;
          [ constructor; [ reflexivity | constructor; simpl; lia ]
          | apply H0; inversion H; subst; reflexivity ]).
      - delta MonotonousMatcher. cbn. intros.
        repeat match goal with
        | [ |- (progress _) _ (if ?b then _ else _) ] => destruct b
        | [ |- (progress _) _ (match ?b with | _ => _ end) ] => destruct b
        end; (apply IHr1 with (str := str) + apply IHr2 with (str := str)); assumption.
      - delta MonotonousMatcher. cbn. intros.
        apply Monotony.repeatMatcher with (str := str); try assumption.
        apply IHr.
      - (* Pesky case which doesn't start like the others *)
        intros. cbn.
        repeat lazymatch goal with
        | [ |- MonotonousMatcher _ _ (if ?b then _ else _) ] => destruct b
        end; delta MonotonousMatcher; cbn; intros;
          [ apply IHr1 with (str := str) | apply IHr2 with (str := str) ]; try apply matcher_to_continuation; auto.
      - delta MonotonousMatcher. cbn. intros.
        specialize (IHr rer dir). delta MonotonousMatcher in IHr. cbn in IHr.
        apply IHr with (str := str); try assumption. delta MonotonousContinuation. cbn. intros.
        repeat match goal with
        | [ |- (progress _) _ (if ?b then _ else _) ] => destruct b
        | [ |- (progress _) _ (match ?b with | _ => _ end) ] => destruct b
        end; try now constructor.
        delta MonotonousContinuation in H.
        inversion H; inversion H1. subst. rewrite <- H3.
        delta MonotonousContinuation in H0. cbn in H0.
        ignore_captures_change.
        apply H0. rewrite <- H3. reflexivity.
      - delta MonotonousMatcher. cbn. intros.
        repeat match goal with
        | [ |- (progress _) _ (if ?b then _ else _) ] => destruct b
        | [ |- (progress _) _ (match ?b with | _ => _ end) ] => destruct b
        end; try now constructor.
        ignore_captures_change. apply H0. assumption.
      Qed.
  End Monotony.


  Lemma ZofNat_is_pos: forall n, (0 <= Z.of_nat n)%Z.
  Proof. induction n; lia. Qed.

  Ltac ztac := repeat match goal with
  | [ H: context[ Z.min ?x ?y] |- _ ] =>
      ( ( assert(x <= y)%Z by lia; replace (Z.min x y) with x in * by (symmetry; apply Z.min_l; assumption) )
      + ( assert(y <= x)%Z by lia; replace (Z.min x y) with y in * by (symmetry; apply Z.min_r; assumption) ) )
  | [ H: context[ Z.of_nat ?n ] |- _ ] => lazymatch goal with
    | [ _: (0 <= Z.of_nat n)%Z |- _ ] => fail
    | [ |- _ ] => pose proof (ZofNat_is_pos n)
    end
  end.

  Ltac check_not_duplicated H :=
    let T := type of H in
    lazymatch goal with
    | [ _: T, _: T |- _ ] => fail
    | [ |- _ ] => idtac
    end.

  Ltac saturate_progress_step dir := match goal with
  | [ H1: progress dir ?x (Success ?y), H2: progress ?dir ?y (Success ?z) |- _ ] =>
    let H := fresh "sp_trans_" H1 H2 in
    pose proof Progress.trans as H;
    specialize H with (1 := H1) (2 := H2);
    check_not_duplicated H
  | [ H1: ?input = MatchState.input ?x,
      H2: ?endIndex = MatchState.endIndex ?x,
      H3: ?y = match_state ?input ?end_index ?c
    |- _ ] => let H := fresh "sp_change_" x y in
              pose proof (Progress.refl dir x) as H;
              apply Progress.ignores_captures with (cx := MatchState.captures x) (cy := c) in H;
              rewrite <- MatchState.reconstruction in H;
              rewrite <- H1 in H;
              rewrite <- H2 in H;
              rewrite <- H3 in H;
              check_not_duplicated H
  end.
  Ltac saturate_progress dir := repeat saturate_progress_step dir.

  Notation "'validState' x" := (0 <= MatchState.endIndex x <= Z.of_nat (length (MatchState.input x)))%Z (at level 99).

  Ltac auto_destruct t := lazymatch t with
  | match ?c with | _ => _ end => let Eq := fresh "MatchEq_" in destruct c eqn:Eq
  | if ?c then _ else _ => let Eq := fresh "IfEq_" in destruct c eqn:Eq
  | ?l _ => auto_destruct l
  end; try discriminate.

  Tactic Notation "focus" constr(f) "auto" "destruct" := (
    assert_type f focus;
    repeat(
      let g := focus_get_goal in
      let t := focus_excise f g in
      auto_destruct t)).

  Tactic Notation "focus" constr(f) "auto" "destruct" "in" hyp(H) := (
    assert_type f focus;
    repeat(
      let g := focus_get_hypothesis H in
      let t := focus_excise f g in
      auto_destruct t)).

  Ltac step_progress := match goal with
  | [ |- progress ?dir _ _ ] => is_constructor dir; constructor; [ reflexivity | constructor; cbn; lia ]
  | [ |- progress ?dir _ _ ] => destruct dir; step_progress
  end.

  Inductive Specialized {A B: Type} (a: A) (b: B) :=
  | AlreadySpecialized: Specialized a b.
  Ltac auto_specialize := repeat match goal with
  | [ a: _, b: _ |- _ ] => lazymatch goal with
    | [ _: Specialized a b |- _ ] => fail
    | [ |- _ ] =>
      pose proof (AlreadySpecialized a b);
      let H := fresh a b in
      pose proof a as H;
      specialize H with (1 := b)
    end
  end.

  Ltac specialize_once := match goal with
  | [ H: _, H': _ |- _ ] => specialize H with (1 := H')
  end.

  Module IntermediateValue.
    Ltac search := try assumption; match goal with
      | [ H: ?c ?y = Success ?z |- exists x, _ /\ ?c x = Success ?z ] => exists y; split; [ try assumption | apply H ]
      end; match goal with
      | [ |- progress ?dir _ _ ] => saturate_progress dir; try assumption
      end.

    Lemma repeatMatcher: forall fuel dir x m min max greedy c groupsWithin z,
          (repeatMatcher' m min max greedy x c groupsWithin fuel) = Success z
      ->  (forall x' c' z', m x' c' = Success z' -> exists y', progress dir x' (Success y') /\ c' y' = Success z')
      ->  exists y, progress dir x (Success y) /\ c y = Success z.
    Proof.
      induction fuel; deltaf repeatMatcher'; cbn; intros;
        focus § _ [] _ § auto destruct in H.
      - discriminate.
      - IntermediateValue.search. apply Progress.refl.
      - auto_specialize; Coq.Program.Tactics.destruct_conjs.
        focus § _ [] _ § auto destruct in H3.
        auto_specialize; Coq.Program.Tactics.destruct_conjs.
        IntermediateValue.search. Progress.clean.
      - IntermediateValue.search. apply Progress.refl.
      - auto_specialize; Coq.Program.Tactics.destruct_conjs.
        focus § _ [] _ § auto destruct in H3.
        auto_specialize; Coq.Program.Tactics.destruct_conjs.
        IntermediateValue.search. Progress.clean.
      - auto_specialize; Coq.Program.Tactics.destruct_conjs.
        focus § _ [] _ § auto destruct in H3.
        auto_specialize; Coq.Program.Tactics.destruct_conjs.
        IntermediateValue.search. Progress.clean.
      - IntermediateValue.search. apply Progress.refl.
    Qed.

    Lemma compileSubPattern: forall r rer dir x c z, (compileSubPattern r rer dir) x c = Success z 
      -> exists y, progress dir x (Success y) /\ c y = Success z.
    Proof.
      induction r; intros rer dir x c z; cbn;
      focus § _ [] _ -> _ § auto destruct; intros.
      + IntermediateValue.search. step_progress.
      + repeat (specialize_once; Coq.Program.Tactics.destruct_conjs). IntermediateValue.search.
      + repeat (specialize_once; Coq.Program.Tactics.destruct_conjs). IntermediateValue.search.
      + apply IntermediateValue.repeatMatcher with (1 := H). intros.
        repeat (specialize_once; Coq.Program.Tactics.destruct_conjs). IntermediateValue.search.
      + repeat (specialize_once; Coq.Program.Tactics.destruct_conjs). IntermediateValue.search.
      + repeat (specialize_once; Coq.Program.Tactics.destruct_conjs). IntermediateValue.search.
      + specialize IHr with (1 := H). Coq.Program.Tactics.destruct_conjs.
        focus §_ [] _§ auto destruct in H1. IntermediateValue.search. Progress.clean.
      + IntermediateValue.search. Progress.clean. apply Progress.refl.
    Qed.
  End IntermediateValue.

  Module Safety.
    Notation "'SafeContinuation' x '|' dir '|' c" := (forall x', validState x' -> progress dir x (Success x') -> c x' <> assertion_failed) 
      (x at level 0, dir at level 0, c at level 0, at level 99).
    Notation "'SafeMatcher' dir '|' m" := (forall x c,
          validState x
      ->  (SafeContinuation x | dir | c)
      ->  m x c <> assertion_failed)
      (dir at level 0, m at level 0, at level 99).

    Lemma continuation_weakening: forall x x' dir (c: MatcherContinuation), progress dir x (Success x')
      -> SafeContinuation x | dir | c -> SafeContinuation x' | dir | c.
    Proof. intros. apply H0; try assumption. saturate_progress dir. assumption. Qed.

    Lemma repeatMatcher: forall fuel dir m min max greedy captures,
      SafeMatcher dir | m -> SafeMatcher dir | (fun x c => repeatMatcher' m min max greedy x c captures fuel).
    Proof.
      induction fuel; intros; cbn; try easy.
      focus § _ (_ [] _) § auto destruct.
      - apply H1; try assumption. apply Progress.refl.
      - apply H; try Progress.clean; try apply Progress.refl.
        intros. focus § _ (_ [] _) § auto destruct.
        apply IHfuel with (dir := dir); try assumption.
        apply Safety.continuation_weakening with (x := x); try assumption.
        Progress.clean.
      - apply H1; try assumption. apply Progress.refl.
      - apply H; try Progress.clean; try apply Progress.refl.
        intros. focus § _ (_ [] _) § auto destruct.
        apply IHfuel with (dir := dir); try assumption.
        apply Safety.continuation_weakening with (x := x); try assumption.
        Progress.clean.
      - apply H; try Progress.clean; try apply Progress.refl.
        intros. focus § _ (_ [] _) § auto destruct.
        apply IHfuel with (dir := dir); try assumption.
        apply Safety.continuation_weakening with (x := x); try assumption.
        Progress.clean.
      - apply H1; try assumption. apply Progress.refl.
    Qed.

    Lemma compileSubPattern: forall r dir rer, SafeMatcher dir | (compileSubPattern r rer dir).
    Proof.
      induction r; cbn; intros;
      focus § _ (_ [] _) § auto destruct.
      - apply H0.
        + destruct dir; cbn in *; constructor; lia.
        + inversion H. destruct dir; (constructor; cbn in *; solve [ assumption | constructor; cbn; lia ]).
      - apply Indexing.failure_kind in MatchEq_0.
        rewrite -> Indexing.failure_bounds in *.
        hypotheses_reflector; destruct dir; cbn in *; lia.
      - auto_specialize. apply IHr1HH0.
      - auto_specialize. apply IHr2HH0.
      - apply Safety.repeatMatcher with (x := x) (dir := dir); try assumption.
        intros. apply IHr; try assumption.
      - intros.
        apply IHr1; try assumption.
        intros. apply IHr2; try assumption.
        apply Safety.continuation_weakening with (x := x); assumption.
      - intros.
        apply IHr2 with (x := x); try assumption.
        intros. apply IHr1; try assumption.
        apply Safety.continuation_weakening with (x := x); assumption.
      - apply IHr with (x := x); try assumption.
        intros. focus § _ (_ [] _) § auto destruct.
        + apply H0; Progress.clean.
        + focus § _ [] _ § auto destruct in MatchEq_;
            destruct dir; try discriminate; inversion H2; inversion H7; spec_reflector Z.leb_spec0; lia.
      - apply H0; Progress.clean. apply Progress.refl.
      - rewrite <- MatchEq_0. apply IHr; try assumption.
        easy.
    Qed.

    Theorem compilePattern: forall r rer input i, 0 <= i <= (length input) -> compilePattern r rer input i <> assertion_failed.
    Proof.
      intros. delta compilePattern. cbn.
      focus § _ (_ [] _) § auto destruct.
      - apply Safety.compileSubPattern.
        + hypotheses_reflector. constructor; cbn; lia.
        + easy.
      - hypotheses_reflector. spec_reflector Nat.leb_spec0. contradiction.
    Qed.
  End Safety.
End Correctness.