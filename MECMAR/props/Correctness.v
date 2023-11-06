From Coq Require Import PeanoNat ZArith Bool Lia Program.Equality.
From Warblre Require Import Tactics Specialize Focus Result Base Patterns StaticSemantics Notation Semantics Definitions.

Import Result.Notations.

Module Correctness.
  Import Patterns.
  Import Notation.
  Import Semantics.

  Notation "'fsuccess' x" := (Success (Some x)) (at level 50, only parsing).

  Create HintDb Warblre.
  #[export] Hint Unfold repeatMatcherFuel : Warblre.
  
  Lemma is_not_failure_true_rewrite: forall (r: MatchResult), r is not failure = true <-> r <> failure.
  Proof. intros [ [ | ] | [ | ] ]; split; easy. Qed.
  Lemma is_not_failure_false_rewrite: forall (r: MatchResult), r is not failure = false <-> r = failure.
  Proof. intros [ [ | ] | [ | ] ]; split; easy. Qed.
  #[export]
  Hint Rewrite -> is_not_failure_true_rewrite is_not_failure_false_rewrite : Warblre.

  (* Lift all computational boolean operators and Z comparisons into Props *)
  Ltac Zhelper := repeat
  (   hypotheses_reflector
  ||  goal_reflector
  ||  normalize_Z_comp
  ||  spec_reflector Z.leb_spec0
  ||  spec_reflector Z.ltb_spec0).


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
    -> progress dir x (fsuccess y)
  | pMismatch: forall dir x, progress dir x (Success None)
  | pError: forall dir x f, progress dir x (Failure f).
  #[export]
  Hint Constructors progress: core.

  Definition OnInput (x: MatchState) (str: list Character) := MatchState.input x = str.
  Definition Valid (x: MatchState) := (0 <= MatchState.endIndex x <= Z.of_nat (length (MatchState.input x)))%Z.

  Module MatchState.
    Lemma characterClass_successful_state_Valid: forall input endIndex captures dir,
      ~ (step{dir} endIndex < 0)%Z  ->
      ~ (Z.of_nat (length input) < step{dir} endIndex)%Z ->
      Valid (Definitions.characterClass_successful_state input endIndex captures dir).
    Proof. destruct dir; constructor; cbn in *; lia. Qed.

    (*  Normalizes all MatchStates by doing the following:
        - Destructing them into their components
        - Then, if the MatchState is known to be on a particular string, eliminate the string introduced at the previous step. *)
    Ltac normalize := repeat
    (   simpl (match_state _ _ _) in *
    ||  simpl (MatchState.input _) in *
    ||  simpl (MatchState.endIndex _) in *
    ||  simpl (MatchState.captures _) in *
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

    Local Ltac solvers := assumption || reflexivity || (Zhelper; apply characterClass_successful_state_Valid; assumption).
    (* Solves the current goal by 1. normalizing the states 2. leveraging assumptions and reflexivity *)
    Ltac solve := normalize; solve [ solvers ].
  End MatchState.

  Module Progress.
    Local Ltac hammer :=
      repeat match goal with
      | [ H: progress _ _ (fsuccess _) |- _ ] => inversion H; clear H; subst
      | [ H: directionalProgress ?d _ _ |- _ ] => is_constructor d; inversion H; clear H
      | [ _: directionalProgress ?d _ _ |- _ ] => destruct d
      | [ |- progress _ _ ?y ] => is_var y; let Eq := fresh "Eq" y in destruct y eqn:Eq
      | [ |- progress _ _ (Success ?y) ] => is_var y; let Eq := fresh "Eq" y in destruct y eqn:Eq
      | [ |- progress ?d _ _ ] => is_constructor d; constructor
      | [ |- progress ?d _ _ ] => destruct d
      | [ |- directionalProgress ?d _ _ ] => is_constructor d; constructor
      | [ |- directionalProgress ?d _ _ ] => destruct d
      end.

    Lemma step: forall x dir, progress dir x (fsuccess (match_state 
        (MatchState.input x)
        (if Direction.eqb dir forward
         then (MatchState.endIndex x + 1)%Z
         else (MatchState.endIndex x - 1)%Z) 
        (MatchState.captures x))).
    Proof. intros. destruct dir; (constructor; cbn in *; solve [ assumption | constructor; cbn; lia ]). Qed.

    Lemma refl: forall dir x, (progress dir) x (fsuccess x).
    Proof. intros. hammer. 1,3: congruence. all: lia. Qed.

    Lemma trans: forall dir x y z, (progress dir) x (fsuccess y) -> (progress dir) y z -> (progress dir) x z.
    Proof.
      intros. hammer.
      1,3: congruence.
      all: lia.
    Qed.

    Lemma ignores_captures_r: forall c1 c2 dir x i n,
          (progress dir) x (fsuccess (i [@ n $ c1]))
      <-> (progress dir) x (fsuccess (i [@ n $ c2])).
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

    Lemma progress_same_input: forall dir x y, progress dir x (fsuccess y)
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
        | [ H: progress _ (?i [@ _ $ _]) (fsuccess (?i [@ _ $ _])) |- _ ] => fail
        | [ H: progress _ (?i1 [@ _ $ _]) (fsuccess (?i2 [@ _ $ _])) |- _ ] =>
          let Tmp := fresh in
          pose proof progress_same_input as Tmp;
          specialize Tmp with (1 := H);
          cbn in Tmp;
          rewrite -> Tmp in *;
          clear Tmp
        end
    ).

    Local Ltac solvers := assumption || apply step || apply refl || reflexivity || MatchState.solve.
    (* Solves the current goal by 1. normalizing progress 2. leveraging assumptions and reflexivity *)
    Ltac solve := normalize; solve [ solvers ].

    Ltac saturate_step := normalize; match goal with
    | [ H1: progress ?dir ?x (fsuccess ?y), H2: progress ?dir ?y (Success ?z) |- _ ] =>
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
    Definition HonoresContinuation (m: Matcher) (dir: direction) := forall x c z, m x c = fsuccess z -> exists y, progress dir x (fsuccess y) /\ c y = fsuccess z.
    #[export]
    Hint Unfold HonoresContinuation : Warblre.

    Ltac search := lazymatch goal with
    | [ H: ?c ?y = fsuccess ?z |- exists x, progress ?dir _ _ /\ ?c x = fsuccess ?z ] =>
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
      + intros. IntermediateValue.search.
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
      (focus § _ _ _ []§ do (fun t => destruct t as [ [ s | ] | ] eqn:Suc)); try easy.
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
      ->  progress dir x0 (fsuccess x) 
      ->  c x <> assertion_failed.
    Definition SafeMatcher (dir: direction) (m: Matcher) :=
      forall x c,
          Valid x
      ->  SafeContinuation x dir c
      ->  m x c <> assertion_failed.
    #[export]
    Hint Unfold SafeContinuation SafeMatcher: Warblre.

    Lemma continuation_weakening: forall x x' dir (c: MatcherContinuation), progress dir x (fsuccess x')
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
      - apply Sc; try Progress.solve.
      - apply Indexing.failure_kind in AutoDest_0.
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
        + focus § _ [] _ § auto destruct in AutoDest_;
            destruct dir; try discriminate; inversion Pxy; inversion H3; Zhelper; lia.
      - apply Sc; Progress.solve.
      - rewrite <- AutoDest_0. apply IHr; try assumption.
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

  Module Termination.
    Definition TerminatingMatcher (m: Matcher) (dir: direction) :=
      forall x c, Valid x -> m x c = out_of_fuel -> exists y, Valid y /\ progress dir x (fsuccess y) /\ c y = out_of_fuel.
    #[export]
    Hint Unfold TerminatingMatcher: Warblre.

    Definition remainingChars (x: MatchState) (dir: direction): nat := match dir with
    | forward => length (MatchState.input x) - Z.to_nat (MatchState.endIndex x)
    | backward => Z.to_nat (MatchState.endIndex x)
    end.
    Definition fuelBound (min: non_neg_integer) (x: MatchState) (dir: direction) := min + (remainingChars x dir)  + 1.
    #[export]
    Hint Unfold fuelBound remainingChars : Warblre.

    Lemma repeatMatcherFuel_satisfies_bound: forall min x dir, Valid x -> fuelBound min x dir <= repeatMatcherFuel min x.
    Proof. intros. autounfold with Warblre in *. unfold Valid in *. destruct dir; cbn; lia. Qed.

    Lemma fuelDecreases_min: forall dir min min' x x' b, 
      min' < min -> progress dir x (fsuccess x') 
      -> fuelBound min x dir <= S b -> fuelBound min' x' dir <= b.
    Proof.
      intros. autounfold with Warblre in *. inversion H0; destruct dir; inversion H6; subst.
      - rewrite -> H3 in *. lia.
      - lia.
    Qed.

    Lemma fuelDecreases_progress: forall dir min x x' b, 
      progress dir x (fsuccess x') -> ((MatchState.endIndex x) =? (MatchState.endIndex x'))%Z = false
      -> Valid x -> Valid x'
      -> fuelBound min x dir <= S b -> fuelBound min x' dir <= b.
    Proof.
      intros. autounfold with Warblre in *. destruct H1. destruct H2. spec_reflector Z.eqb_spec.
      destruct dir; inversion H.
      - inversion H10. subst. rewrite -> H7 in *. lia.
      - inversion H10. lia.
    Qed.

    Ltac boolean_simplifier := repeat
    (   rewrite -> andb_true_l in *
    ||  match goal with
        | [ H: ?c1 = ?c2 |- _ ] => check_type c1 bool; is_constructor c1; is_constructor c2; try discriminate H; clear H
        | [ H: ?b = _ |- _ ] => check_type b bool; is_constructor b; symmetry in H
        | [ H: _ = ?b |- _ ] => rewrite -> H in *
        | [ H: negb _ = _ |- _ ] => apply (f_equal negb) in H; rewrite -> negb_involutive in H; cbn in H
        end).

    Ltac search := lazymatch goal with
    | [ H: ?c ?y = out_of_fuel |- exists x, Valid x /\ progress ?dir _ _ /\ ?c x = out_of_fuel ] =>
      exists y; split; [ | split ];
      [ try solve [Progress.saturate]
      | try solve [Progress.saturate]
      | apply H ]
    end.

    Lemma repeatMatcher': forall fuel m min max greedy captures x c dir, fuelBound min x dir <= fuel -> Valid x ->
      TerminatingMatcher m dir ->
      repeatMatcher' m min max greedy x c captures fuel = out_of_fuel ->
      exists y, Valid y /\ progress dir x (fsuccess y) /\ c y = out_of_fuel.
    Proof.
      induction fuel; intros m min max greedy captures x c dir INEQ_fuel Vx Tm Falsum.
      - autounfold with Warblre in *. lia.
      - cbn in Falsum.
        (focus § _ [] _ § auto destruct in Falsum).
        + search.
        + apply Tm in Falsum; try Progress.solve. destruct Falsum as [ y [ Vy [ Pxy Falsum ] ] ].
          (focus § _ [] _ § auto destruct in Falsum). boolean_simplifier.
          assert(FD: fuelBound (min - 1) y dir <= fuel). {
            apply fuelDecreases_min with (min := min) (x := x); try Progress.solve.
            spec_reflector Nat.eqb_spec. lia.
          }
          specialize IHfuel with (1 := FD) (2 := Vy) (3 := Tm) (4 := Falsum). clear Falsum.
          destruct IHfuel as [ z [ Vz [ Pyz Falsum ] ] ].
          search.
        + search.
        + apply Tm in Falsum; try Progress.solve. destruct Falsum as [ y [ Vy [ Pxy Falsum ] ] ].
          (focus § _ [] _ § auto destruct in Falsum).
          boolean_simplifier. spec_reflector Nat.eqb_spec. subst.
          assert(FD: fuelBound 0 y dir <= fuel). {
            (focus § _ [] _ § do (fun t => apply fuelDecreases_progress with (x := t)) in Pxy); try Progress.solve.
            MatchState.normalize. spec_reflector Z.eqb_spec. congruence.
          }
          specialize IHfuel with (1 := FD) (2 := Vy) (3 := Tm) (4 := Falsum). clear Falsum.
          destruct IHfuel as [ z [ Vz [ Pyz Falsum ] ] ].
          search.
        + apply Tm in Falsum; try Progress.solve. destruct Falsum as [ y [ Vy [ Pxy Falsum ] ] ].
          (focus § _ [] _ § auto destruct in Falsum).
          boolean_simplifier. spec_reflector Nat.eqb_spec. subst.
          assert(FD: fuelBound 0 y dir <= fuel). {
            (focus § _ [] _ § do (fun t => apply fuelDecreases_progress with (x := t)) in Pxy); try Progress.solve.
            MatchState.normalize. spec_reflector Z.eqb_spec. congruence.
          }
          specialize IHfuel with (1 := FD) (2 := Vy) (3 := Tm) (4 := Falsum). clear Falsum.
          destruct IHfuel as [ z [ Vz [ Pyz Falsum ] ] ].
          search.
        + search.
    Qed.

    Lemma repeatMatcher: forall m min max greedy captures dir,
      TerminatingMatcher m dir -> TerminatingMatcher (fun x c => repeatMatcher m min max greedy x c captures) dir.
    Proof. unfold Semantics.repeatMatcher, TerminatingMatcher. intros.
      pose proof repeatMatcher' as Tmp. specialize Tmp with (4 := H1). apply Tmp; try easy.
      apply repeatMatcherFuel_satisfies_bound. assumption.
    Qed.

    Lemma compileSubPattern: forall r rer dir, TerminatingMatcher (compileSubPattern r rer dir) dir.
    Proof.
      induction r; intros rer dir; cbn -[Semantics.repeatMatcher];
      focus § _ [] _ § auto destruct.
      - intros x c Vx H. autounfold with Warblre in *. focus § _ [] _ § auto destruct in H.
        + search.
        + apply Indexing.failure_is_assertion in AutoDest_0. simpl in AutoDest_0. congruence.
      - intros x c Vx H. autounfold with Warblre in *. focus § _ [] _ § auto destruct in H; repeat (specialize_once; Coq.Program.Tactics.destruct_conjs); search.
      - apply repeatMatcher. apply IHr.
      - intros x c Vx H. autounfold with Warblre in *. repeat (auto_specialize; Coq.Program.Tactics.destruct_conjs). search.
      - intros x c Vx H. autounfold with Warblre in *. repeat (auto_specialize; Coq.Program.Tactics.destruct_conjs). search.
      - intros x c Vx H. autounfold with Warblre in *. repeat (auto_specialize; Coq.Program.Tactics.destruct_conjs).
        focus § _ [] _ § auto destruct in H4.
        + search.
        + focus § _ [] _ § auto destruct in AutoDest_; congruence.
      - intros x c Vx H. autounfold with Warblre in *.
        focus § _ [] _ § auto destruct in H.
        + search.
        + rewrite -> H in *; clear H. repeat (auto_specialize; Coq.Program.Tactics.destruct_conjs). discriminate.
    Qed.

    Lemma compilePattern: forall r rer input i, compilePattern r rer input i <> out_of_fuel.
    Proof.
      intros. delta compilePattern. cbn.
      focus § _ (_ [] _) § auto destruct.
      (focus § _ (_ [] _) § do (fun t => destruct t eqn:S)); try easy.
      destruct f; try easy.
      pose proof compileSubPattern as Falsum. autounfold with Warblre in *. specialize Falsum with (2 := S).
      focus § _ [] -> _ § do (fun t => assert(Valid t)) in Falsum.
      - spec_reflector Nat.leb_spec0. constructor; cbn; lia.
      - specialize Falsum with (1 := H). Coq.Program.Tactics.destruct_conjs. discriminate.
    Qed.

    From Coq Require Import Logic.FunctionalExtensionality.
    Definition TerminatingContinuation (c: MatcherContinuation) :=
      forall x, c x <> out_of_fuel.
    Lemma repeatMatcher_fuelWeakening: forall fuelL fuelH (m: Matcher) min max greedy captures x c dir, fuelL <= fuelH ->
      TerminatingMatcher m dir -> IntermediateValue.HonoresContinuation m dir -> TerminatingContinuation c ->
      Semantics.repeatMatcher' m min max greedy x c captures fuelL <> out_of_fuel -> 
      Semantics.repeatMatcher' m min max greedy x c captures fuelH = Semantics.repeatMatcher' m min max greedy x c captures fuelL.
    Proof.
      induction fuelL; intros fuelH m min max greedy captures x c dir INEQ_fuel Tm Hm Tc Tl; [ easy | ].
      apply Nat.lt_exists_pred in INEQ_fuel. destruct INEQ_fuel as [ fuelH' [ EQ_fuelH INEQ_fuel ] ].
      subst. rename fuelH' into fuelH.
      cbn in Tl |- *.
      (focus § _ (_ [] _) § auto destruct in Tl); try easy.
      - (* How to go from Tl to the hypothesis of IHfuelL? *)
        (* We are in the case min > 0, i.e. we need to eat *)
        (focus § _ (_ [] _) § do (fun t => destruct t eqn:Eq in Tl) in Tl).
        + (* pose proof Eq as Eq'.
          apply Hm in Eq. destruct Eq as [ y [Pxy Eq] ].
          (focus § _ [] _ § auto destruct in Eq).
          focus § _ [] _ § do (fun t => assert (NEQ: t <> out_of_fuel) by congruence) in Eq.
          specialize IHfuelL with (1 := INEQ_fuel) (2 := Tm) (3 := Hm) (4 := Tc) (5 := NEQ).
          rewrite -> Eq'. rewrite <- Eq. rewrite <- IHfuelL. *)
          (* How does one show that y is the value privded to the continuation? *)
          f_equal. apply functional_extensionality. intros y.
          (focus § _ [] _ § auto destruct); try easy.
          apply IHfuelL with (dir := dir); try assumption.
          (* Intermediate value doesn't help; we have no way of connecting it to y *)
          admit.
        + destruct f; try easy.
          (*  If m was systematically failing, this could hide termination issues in its continuation,
                which must terminate in order to apply the IH *)
          admit.
      - admit.
      - (focus § _ (_ [] _) § do (fun t => destruct t as [ [ s | ] | ] eqn:Eq in Tl) in Tl).
        + apply Hm in Eq. destruct Eq as [ y [Pxy Eq] ].
          (focus § _ [] _ § auto destruct in Eq).
          rewrite <- Eq in Tl.
          admit.
        + admit.
        + admit.
      - admit.
    Abort.
  End Termination.
End Correctness.