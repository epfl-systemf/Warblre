From Coq Require Import PeanoNat ZArith Bool Lia Program.Equality.
From Warblre Require Import Tactics Specialize Focus Result Base Patterns StaticSemantics Notation Semantics.

Import Result.Notations.

Module Correctness.
  Import Patterns.
  Import Notation.
  Import Semantics.

  Create HintDb warblre.

  (* Lift all computational boolean operators and Z comparisons into Props *)
  Ltac Zhelper := repeat
  (   hypotheses_reflector
  ||  goal_reflector
  ||  normalize_Z_comp
  ||  spec_reflector Z.leb_spec0
  ||  spec_reflector Z.ltb_spec0).

  (* Notation for MatchStates which goes nicely with the normalization tactic *)
  Notation "s '[@' n '$' c ']'" := (match_state s n c) (at level 50, left associativity).

  (** Progress: We say that a MatchState (wrapped in Result) ry has progressed w.r.t to another MatchState x if:
      - ry = Success y, x and y share the same input string and either
        + direction is forward, in which case x's endIndex <= y's endIndex
        + direction is backward, in which case y's endIndex <= x's endIndex
      - ry is any kind of failure
  *)

  (* Allows to abstract most theorem over the direction of progress *)
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
    (*  Normalizes all MatchStates by doing the following:
        - Destructing them into their components
        - Then, if the MatchState is known to be on a particular string, eliminate the string introduced at the previous step. *)
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

    (*  Normalize the hypotheses/goals related to progress:
        - Normalize all MatchStates (using MatchState.normalize)
        - Uniformizes all captures, which are irrelevant to progress (replaces all of them by DMap.empty)
        - Derives that two MatchStates have the same input from progress hypotheses *)
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
    (* Solves the current goal by 1. normalizing progress 2. leveraging assumptions and reflexivity *)
    Ltac solve := normalize; solve [ solvers ].

    Ltac saturate_step := normalize; match goal with
    | [ H1: progress ?dir ?x (Success ?y), H2: progress ?dir ?y (Success ?z) |- _ ] =>
      let H := fresh "ps_trans_" H1 H2 in
      pose proof Progress.trans as H;
      specialize H with (1 := H1) (2 := H2);
      check_not_duplicated H
    end.

    (* Saturates the progress hypotheses by transitivity. Then attemps to solve goals using assumptions and reflexivity. *)
    Ltac saturate := repeat (normalize; saturate_step); normalize; try solvers.
  End Progress.

  (** Intermediate value: We say that Matcher _honores its continuation_ if 
      its continuation must succeed on an input the matcher called it with in order for the matcher to itself succeed. *)
  Module IntermediateValue.
    (* y is also most likely Valid; see if we can incorporate this to the definition *)
    Definition HonoresContinuation (m: Matcher) (dir: direction) := forall x c z, m x c = Success z -> exists y, progress dir x (Success y) /\ c y = Success z.
    #[export]
    Hint Unfold HonoresContinuation : Warblre.

    Ltac search := lazymatch goal with
    | [ H: ?c ?y = Success ?z |- exists x, progress ?dir _ _ /\ ?c x = Success ?z ] =>
      exists y; split;
      [ try solve [Progress.saturate]
      | apply H ]
    end.

    Lemma repeatMatcher: forall fuel dir m min max greedy groupsWithin,
          HonoresContinuation m dir -> HonoresContinuation (fun x c => repeatMatcher' m min max greedy x c groupsWithin fuel) dir.
    Proof.
      induction fuel; [ discriminate | ].
      deltaf repeatMatcher'. cbn. intros dir m min max greedy groupsWithin HCm x c z H.
      focus § _ [] _ § auto destruct in H; autounfold with Warblre in *.
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

    Lemma compileSubPattern: forall r rer dir, HonoresContinuation (compileSubPattern r rer dir) dir.
    Proof.
      induction r; intros rer dir x c z; cbn;
      focus § _ [] _ -> _ § auto destruct.
      + intros. IntermediateValue.search. destruct dir; (constructor; [ reflexivity | constructor; cbn; lia ]).
      + intros. autounfold with Warblre in *. repeat (specialize_once; Coq.Program.Tactics.destruct_conjs). IntermediateValue.search.
      + intros. autounfold with Warblre in *. repeat (specialize_once; Coq.Program.Tactics.destruct_conjs). IntermediateValue.search.
      + apply IntermediateValue.repeatMatcher. apply IHr.
      + intros. autounfold with Warblre in *. repeat (specialize_once; Coq.Program.Tactics.destruct_conjs). IntermediateValue.search.
      + intros. autounfold with Warblre in *. repeat (specialize_once; Coq.Program.Tactics.destruct_conjs). IntermediateValue.search.
      + intros. autounfold with Warblre in *. repeat (specialize_once; Coq.Program.Tactics.destruct_conjs).
        focus §_ [] _§ auto destruct in H1. IntermediateValue.search.
      + intros. IntermediateValue.search.
    Qed.
  End IntermediateValue.

  (** Monotony: We say that Matcher(Continuation) is
    + A _Forward_ Matcher(Continuation) if for any input (x: MatchState), the then returned (y: MatchState) is a foward progress;
    + A _Backward_ Matcher(Continuation) if for any input (x: MatchState), the then returned (y: MatchState) is a backward progress;
    + A _Stationary_ Matcher(Continuation) if it is both a Forward and Backward Matcher(Continuation). *)
  Module Monotony.
    Definition MonotonousContinuation (dir: direction) (c: MatcherContinuation) :=
      forall x, (progress dir) x (c x).
    Definition MonotonousMatcher (dir: direction) (m: Matcher) :=
      forall x c,
          MonotonousContinuation dir c
      ->  progress dir x (m x c).
    #[export]
    Hint Unfold MonotonousContinuation MonotonousMatcher : Warblre.

    Lemma compileSubPattern: forall r rer dir, MonotonousMatcher dir (compileSubPattern r rer dir).
    Proof.
      intros r rer dir x c Mc.
      (focus § _ _ _ []§ do (fun t => destruct t eqn:Suc)); try easy.
      apply IntermediateValue.compileSubPattern with (dir := dir) in Suc.
      destruct Suc as [ y [ Pxy Suc ] ]. rewrite <- Suc.
      apply Progress.trans with (y := y).
      + assumption.
      + apply Mc.
    Qed.

    Lemma compilePattern: forall r rer input i, progress forward (match_state input (Z.of_nat i) (DMap.empty CaptureRange)) (compilePattern r rer input i).
    Proof.
      intros. delta compilePattern. cbn.
      focus § _ _ _ [] § auto destruct.
      - apply compileSubPattern.
        intros x. apply Progress.refl.
      - constructor.
    Qed.
  End Monotony.

  Module Safety.
    Definition SafeContinuation (x0: MatchState) (dir: direction) (c: MatcherContinuation) :=
      forall x,
          Valid x
      ->  progress dir x0 (Success x) 
      ->  c x <> assertion_failed.
    Definition SafeMatcher (dir: direction) (m: Matcher) :=
      forall x c,
          Valid x
      ->  SafeContinuation x dir c
      ->  m x c <> assertion_failed.
    #[export]
    Hint Unfold SafeContinuation SafeMatcher: Warblre.

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