From Coq Require Import PeanoNat ZArith Bool Lia Program.Equality.
From Warblre Require Import Tactics Specialize Focus Result Base Patterns StaticSemantics Notation Semantics.

Import Result.Notations.

Module Correctness.
  Import Patterns.
  Import Notation.
  Import Semantics.

  Create HintDb warblre.

  Ltac Zhelper := repeat
  (   hypotheses_reflector
  ||  goal_reflector
  ||  normalize_Z_comp
  ||  spec_reflector Z.leb_spec0
  ||  spec_reflector Z.ltb_spec0).

  Notation "s '[@' n '$' c ']'" := (match_state s n c) (at level 50, left associativity).

  Inductive directionalProgress: direction -> MatchState -> MatchState -> Prop :=
  | dpForward: forall x y, (MatchState.endIndex x <= MatchState.endIndex y)%Z -> directionalProgress forward x y
  | dpBackward: forall x y, (MatchState.endIndex x >= MatchState.endIndex y)%Z -> directionalProgress backward x y.

  Inductive progress: direction -> MatchState -> MatchResult -> Prop :=
  | pStep: forall dir x y, 
      (MatchState.input x) = (MatchState.input y)
    -> directionalProgress dir x y
    -> progress dir x (Success y)
  | pFail: forall dir x f, progress dir x (Failure f).
  #[export]
  Hint Constructors progress: core.

  Definition OnInput (x: MatchState) (str: list Character) := MatchState.input x = str.
  Definition Valid (x: MatchState) := (0 <= MatchState.endIndex x <= Z.of_nat (length (MatchState.input x)))%Z.
  Module MatchState.
    Ltac normalize := repeat
    (   simpl (match_state _ _ _) in *
    ||  lazymatch goal with
        | [ x: MatchState |- _ ] =>
          let input := fresh "input_" x in
          let endIndex := fresh "endIndex_" x in
          let captures := fresh "captures_" x in
          destruct x as [ input endIndex captures ]
        | [ H: OnInput (match_state ?input _ _) ?str |- _ ] =>
          unfold OnInput in H; cbn in H;
          try rewrite -> H in *; clear H; clear input
        end).
  End MatchState.

  Module Progress.
    Local Ltac hammer :=
      repeat match goal with
      | [ H: progress _ _ (Success _) |- _ ] => inversion H; clear H; subst
      | [ H: directionalProgress ?d _ _ |- _ ] => is_constructor d; inversion H; clear H
      | [ _: directionalProgress ?d _ _ |- _ ] => destruct d
      | [ |- progress _ _ ?y ] => is_var y; let Eq := fresh "Eq" y in destruct y eqn:Eq
      | [ |- progress ?d _ _ ] => is_constructor d; constructor
      | [ |- progress ?d _ _ ] => destruct d
      | [ |- directionalProgress ?d _ _ ] => is_constructor d; constructor
      | [ |- directionalProgress ?d _ _ ] => destruct d
      end.

    Lemma refl: forall dir x, (progress dir) x (Success x).
    Proof. intros. hammer. 1,3: congruence. all: lia. Qed.

    Lemma trans: forall dir x y z, (progress dir) x (Success y) -> (progress dir) y z -> (progress dir) x z.
    Proof.
      intros. hammer.
      1,3: congruence.
      all: lia.
    Qed.

    Lemma ignores_captures_r: forall c1 c2 dir x i n,
          (progress dir) x (Success (i [@ n $ c1]))
      <-> (progress dir) x (Success (i [@ n $ c2])).
    Proof.
      intros; split; intros; hammer; subst.
      all: try assumption.
      all: cbn in *; lia.
    Qed.

    Lemma ignores_captures_l: forall c1 c2 dir i n y,
          (progress dir) (i [@ n $ c1]) (Success y)
      <-> (progress dir) (i [@ n $ c2]) (Success y).
    Proof.
      intros; split; intros; hammer; subst.
      all: try assumption.
      all: cbn in *; lia.
    Qed.

    Lemma progress_same_input: forall dir x y, progress dir x (Success y)
      -> MatchState.input x = MatchState.input y.
    Proof. intros. inversion H. assumption. Qed.

    Ltac normalize := repeat (
        MatchState.normalize
    ||  rewrite <- (ignores_captures_l (DMap.empty _)) in *
    ||  rewrite <- (ignores_captures_r (DMap.empty _)) in *
    ||  lazymatch goal with
        | [ H: progress _ (?i [@ _ $ _]) (Success (?i [@ _ $ _])) |- _ ] => fail
        | [ H: progress _ (?i1 [@ _ $ _]) (Success (?i2 [@ _ $ _])) |- _ ] =>
          let Tmp := fresh in
          pose proof progress_same_input as Tmp;
          specialize Tmp with (1 := H);
          cbn in Tmp;
          rewrite -> Tmp in *;
          clear Tmp
        end
    ).

    Local Ltac solvers := assumption || apply refl || reflexivity.
    Ltac solve := normalize; solve [ solvers ].

    Ltac saturate_step := normalize; match goal with
    | [ H1: progress ?dir ?x (Success ?y), H2: progress ?dir ?y (Success ?z) |- _ ] =>
      let H := fresh "ps_trans_" H1 H2 in
      pose proof Progress.trans as H;
      specialize H with (1 := H1) (2 := H2);
      check_not_duplicated H
    end.
    Ltac saturate := repeat (normalize; saturate_step); normalize; try solvers.
  End Progress.

  Module Monotony.
    Definition MonotonousContinuation (dir: direction) (str: list Character) (c: MatcherContinuation) := forall x, OnInput x str -> (progress dir) x (c x).
    Definition MonotonousMatcher (dir: direction) (str: list Character) (m: Matcher) := 
      forall x c, OnInput x str -> MonotonousContinuation dir str c -> (progress dir) x (m x c).

    Lemma matcher_to_continuation: forall dir str m c, MonotonousMatcher dir str m -> MonotonousContinuation dir str c
      -> MonotonousContinuation dir str (fun (x: MatchState) => m x c).
    Proof. intros. unfold MonotonousContinuation. intros. apply H; assumption. Qed.

    Ltac check_type t T := lazymatch type of t with
    | T => idtac
    | _ => fail
    end.
    Ltac obvious_transitivity := match goal with
      | [ |- progress _ _ (?m ?y' _) ] => check_type m Matcher; apply Progress.trans with (y := y')
      | [ |- progress _ _ (?c ?y') ] => check_type c MatcherContinuation; apply Progress.trans with (y := y')
      end.

    Lemma repeatMatcher: forall fuel dir str x m min max greedy c groupsWithin,
              MonotonousMatcher dir str m
          ->  MonotonousContinuation dir str c
          ->  OnInput x str
          ->  progress dir x (repeatMatcher' m min max greedy x c groupsWithin fuel).
    Proof.
      induction fuel; try constructor.
      intros. cbn.
      focus § _ _ _ [] § auto destruct.
      - apply H0; assumption.
      - obvious_transitivity; [ Progress.solve | ].
        apply H; try assumption.
        cbn. intros x' OIx'. focus § _ _ _ [] § auto destruct; try easy.
        apply IHfuel with (str := str); assumption.
      - apply H0; assumption.
      - obvious_transitivity; [ Progress.solve | ].
        apply H; try assumption.
        cbn. intros x' OIx'. focus § _ _ _ [] § auto destruct; try easy.
        apply IHfuel with (str := str); assumption.
      - obvious_transitivity; [ Progress.solve | ].
        apply H; try assumption.
        cbn. intros x' OIx'. focus § _ _ _ [] § auto destruct; try easy.
        apply IHfuel with (str := str); assumption.
      - apply H0; assumption.
    Qed.

    Lemma compileSubPattern: forall r rer dir str, MonotonousMatcher dir str (compileSubPattern r rer dir).
    Proof.
      induction r; intros; intros x c OIx Mc; cbn.
      - focus § _ _ _ []§ auto destruct; try easy.
        destruct dir;
          (obvious_transitivity;
          [ constructor; [ reflexivity | constructor; cbn; lia ]
          | apply Mc; inversion OIx; subst; reflexivity ]).
      - focus § _ _ _ []§ auto destruct; (apply IHr1 with (str := str) + apply IHr2 with (str := str)); assumption.
      - apply Monotony.repeatMatcher with (str := str); try assumption.
        apply IHr.
      - focus § _ _ _ []§ auto destruct.
        + apply IHr1 with (str := str); try assumption.
          intros x' OIx'.
          apply IHr2 with (str := str); try assumption.
        + apply IHr2 with (str := str); try assumption.
          intros x' OIx'.
          apply IHr1 with (str := str); try assumption.
      - apply IHr with (str := str); try assumption. cbn. intros x' OIx'.
        focus § _ _ _ []§ auto destruct; try easy.
        Progress.normalize.
        obvious_transitivity.
        + Progress.solve.
        + apply Mc. Progress.solve.
      - focus § _ _ _ []§ auto destruct; try easy.
        obvious_transitivity.
        + Progress.solve.
        + apply Mc. Progress.solve.
      Qed.

      Lemma compilePattern: forall r rer input i, progress forward (match_state input (Z.of_nat i) (DMap.empty CaptureRange)) (compilePattern r rer input i).
      Proof.
        intros. delta compilePattern. cbn.
        remember (match_state input (Z.of_nat i) (DMap.empty CaptureRange)) as x.
        focus § _ _ _ [] § auto destruct.
        - pose proof compileSubPattern. unfold MonotonousMatcher in H.
          apply H with (str := input).
          + subst. reflexivity.
          + intros y OIy. apply Progress.refl.
        - constructor.
      Qed.
  End Monotony.

  Ltac step_progress := match goal with
  | [ |- progress ?dir _ _ ] => is_constructor dir; constructor; [ reflexivity | constructor; cbn; lia ]
  | [ |- progress ?dir _ _ ] => destruct dir; step_progress
  end.

  Module IntermediateValue.
    Ltac search := try assumption; match goal with
      | [ H: ?c ?y = Success ?z |- exists x, _ /\ ?c x = Success ?z ] => exists y; split; [ try assumption | apply H ]
      end; match goal with
      | [ |- progress ?dir _ _ ] => Progress.saturate
      end.

    Lemma repeatMatcher: forall fuel dir x m min max greedy c groupsWithin z,
          (repeatMatcher' m min max greedy x c groupsWithin fuel) = Success z
      ->  (forall x' c' z', m x' c' = Success z' -> exists y', progress dir x' (Success y') /\ c' y' = Success z')
      ->  exists y, progress dir x (Success y) /\ c y = Success z.
    Proof.
      induction fuel; deltaf repeatMatcher'; cbn; intros;
        focus § _ [] _ § auto destruct in H.
      - discriminate.
      - IntermediateValue.search.
      - auto_specialize; Coq.Program.Tactics.destruct_conjs.
        focus § _ [] _ § auto destruct in H3.
        auto_specialize; Coq.Program.Tactics.destruct_conjs.
        IntermediateValue.search.
      - IntermediateValue.search.
      - auto_specialize; Coq.Program.Tactics.destruct_conjs.
        focus § _ [] _ § auto destruct in H3.
        auto_specialize; Coq.Program.Tactics.destruct_conjs.
        IntermediateValue.search.
      - auto_specialize; Coq.Program.Tactics.destruct_conjs.
        focus § _ [] _ § auto destruct in H3.
        auto_specialize; Coq.Program.Tactics.destruct_conjs.
        IntermediateValue.search.
      - IntermediateValue.search.
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
        focus §_ [] _§ auto destruct in H1. IntermediateValue.search.
      + IntermediateValue.search.
    Qed.
  End IntermediateValue.

  Module Safety.
    Definition SafeContinuation (x: MatchState) (dir: direction) (c: MatcherContinuation) := (forall x', Valid x' -> progress dir x (Success x') -> c x' <> assertion_failed).
    Definition SafeMatcher (dir: direction) (m: Matcher) := (forall x c,
          Valid x
      ->  (SafeContinuation x dir c)
      ->  m x c <> assertion_failed).

    Lemma continuation_weakening: forall x x' dir (c: MatcherContinuation), progress dir x (Success x')
      -> SafeContinuation x dir c -> SafeContinuation x' dir c.
    Proof. intros. intros y Vy Pxy. apply H0; try assumption. Progress.saturate. Qed.

    Lemma repeatMatcher: forall fuel dir m min max greedy captures,
      SafeMatcher dir m -> SafeMatcher dir (fun x c => repeatMatcher' m min max greedy x c captures fuel).
    Proof.
      induction fuel; intros; intros x c Vx Sc; cbn; try easy.
      focus § _ (_ [] _) § auto destruct.
      - apply Sc; try assumption. apply Progress.refl.
      - apply H; try Progress.solve.
        intros y Vy Pxy. focus § _ (_ [] _) § auto destruct.
        apply IHfuel with (dir := dir); try assumption.
        apply Safety.continuation_weakening with (x := x); try assumption.
        Progress.solve.
      - apply Sc; try assumption. apply Progress.refl.
      - apply H; try Progress.solve.
        intros y Vy Pxy. focus § _ (_ [] _) § auto destruct.
        apply IHfuel with (dir := dir); try assumption.
        apply Safety.continuation_weakening with (x := x); try assumption.
        Progress.solve.
      - apply H; try Progress.solve.
        intros y Vy Pxy. focus § _ (_ [] _) § auto destruct.
        apply IHfuel with (dir := dir); try assumption.
        apply Safety.continuation_weakening with (x := x); try assumption.
        Progress.solve.
      - apply Sc; try assumption. apply Progress.refl.
    Qed.

    Lemma compileSubPattern: forall r dir rer, SafeMatcher dir (compileSubPattern r rer dir).
    Proof.
      induction r; cbn; intros dir rer x c Vx Sc;
      focus § _ (_ [] _) § auto destruct.
      - apply Sc.
        + destruct dir; constructor; cbn in *; lia.
        + inversion Vx. destruct dir; (constructor; cbn in *; solve [ assumption | constructor; cbn; lia ]).
      - apply Indexing.failure_kind in MatchEq_0.
        rewrite -> Indexing.failure_bounds in *.
        unfold Valid in *. destruct dir; cbn in *; Zhelper; try lia.
      - apply IHr1; assumption.
      - apply IHr2; assumption.
      - apply Safety.repeatMatcher with (x := x) (dir := dir); try assumption.
        intros. apply IHr; try assumption.
      - intros.
        apply IHr1; try assumption.
        intros y Vy Pxy. apply IHr2; try assumption.
        apply Safety.continuation_weakening with (x := x); assumption.
      - intros.
        apply IHr2 with (x := x); try assumption.
        intros y Vy Pxy. apply IHr1; try assumption.
        apply Safety.continuation_weakening with (x := x); assumption.
      - apply IHr with (x := x); try assumption.
        intros y Vy Pxy. focus § _ (_ [] _) § auto destruct.
        + apply Sc; Progress.solve.
        + focus § _ [] _ § auto destruct in MatchEq_;
            destruct dir; try discriminate; inversion Pxy; inversion H3; Zhelper; lia.
      - apply Sc; Progress.solve.
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