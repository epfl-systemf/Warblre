From Coq Require Import PeanoNat ZArith Bool Lia Program.Equality List.
From Warblre Require Import List Tactics Specialize Focus Result Base Patterns StaticSemantics Notation Semantics Definitions EarlyErrors.

Import Result.Notations.
Import Semantics.
Import Coercions.

Module Correctness.
  Import Patterns.
  Import Notation.
  Import Semantics.

  Lemma canonicalize_success: forall rer a, exists v, canonicalize rer a = Success v.
  Proof.
    intros. remember (canonicalize rer a) as r eqn:C. unfold canonicalize in C.
    focus § _ _ [] § auto destruct in C; try solve [ focus § _ _ (_ []) § do (fun v => exists v) in C; subst; reflexivity ].
    - hypotheses_reflector. spec_reflector Nat.eqb_spec. apply List.Unique.failure_bounds in AutoDest_2. easy.
  Qed.

  Ltac rewrite_canonicalize := repeat lazymatch goal with 
        | [ H: context[ canonicalize ?rer ?c ] |- _ ] =>
            lazymatch goal with
            | [ _: canonicalize rer c = Success _ |- _ ] => idtac
            | [ |- _ ] =>
                let d := fresh "canonicalized_" c in
                let Eq := fresh "Eq_" d in
                pose proof (canonicalize_success rer c) as [ d Eq ];
                rewrite -> Eq in *
            end
        end.

  Lemma is_not_failure_true_rewrite: forall (r: option MatchState), r is not failure = true <-> r <> failure.
  Proof. intros [ | ]; split; easy. Qed.
  Lemma is_not_failure_false_rewrite: forall (r: option MatchState), r is not failure = false <-> r = failure.
  Proof. intros [ ]; split; easy. Qed.
  #[export]
  Hint Rewrite -> is_not_failure_true_rewrite is_not_failure_false_rewrite : Warblre.

  Ltac clean := repeat
  (   unfold wrap_option,CaptureRange_or_undefined in *
  ||  lazymatch goal with
      | [ Eq: Success _ = Success _ |-_] => injection Eq as Eq
      end).


  (** Progress: We say that a MatchState (wrapped in Result) ry has progressed w.r.t to another MatchState x if:
      - ry = Success y, x and y share the same input string and either
        + direction is forward, in which case x's endIndex <= y's endIndex
        + direction is backward, in which case y's endIndex <= x's endIndex
      - ry is any kind of failure
  *)

  Module Captures.
    Definition Valid (rer: RegExp) (parenIndex parenCount: non_neg_integer) :=
      List.Forall.Forall (List.Range.Nat.Bounds.range (parenIndex) (parenIndex + parenCount)) (fun i => i < RegExp.capturingGroupsCount rer).
  End Captures.

  (* Allows to abstract most theorem over the direction of progress *)
  Inductive directionalProgress: direction -> MatchState -> MatchState -> Prop :=
  | dpForward: forall x y, (MatchState.endIndex x <= MatchState.endIndex y)%Z -> directionalProgress forward x y
  | dpBackward: forall x y, (MatchState.endIndex x >= MatchState.endIndex y)%Z -> directionalProgress backward x y.

  Inductive progress: direction -> MatchState -> MatchResult -> Prop :=
  | pStep: forall dir x y, 
      (MatchState.input x) = (MatchState.input y)
    -> directionalProgress dir x y
    -> progress dir x (Success (Some y))
  | pMismatch: forall dir x, progress dir x failure
  | pError: forall dir x f, progress dir x (Failure f).
  #[export]
  Hint Constructors progress: core.

  Definition IteratorOn (str: list Character) (i: Z) := (0 <= i <= Z.of_nat (length str))%Z.

  Module CaptureRange.
    Inductive Valid (str: list Character): option CaptureRange -> Prop :=
    | vCrDefined: forall s e, ( s <= e -> IteratorOn str s -> IteratorOn str e -> Valid str (Some (capture_range s e)) )%Z
    | vCrUndefined: Valid str undefined.

    Ltac normalize := repeat
    (   cbn
    ||  unfold wrap_option,CaptureRange_or_undefined in *
    ||  unfold IteratorOn in *
    ||  match goal with
        | [ Eq: Success (capture_range _ _ _) = Success ?s |-_] => injection Eq as <-
        | [ Eq: Success ?s = Success (capture_range _ _ _) |-_] => injection Eq as ->
        | [ c: CaptureRange |- _ ] => let s := fresh c "_start" in
                                      let e := fresh c "_end" in
                                      destruct c as [ s e ]
        | [ VCs : List.Forall.Forall ?c (CaptureRange.Valid ?str),
            Indexed : (?c [?n]) = Success (Some (capture_range ?s ?e))
          |- _ ] => is_var c; lazymatch goal with
                    | [ _: (s <= e)%Z |- _ ] => fail
                    | [ |- _ ] => let H := fresh "VCR_" s "_" e in
                                  cbn in Indexed; focus § _ [] _ § auto destruct in Indexed;
                                  pose proof (VCs _ _ Indexed) as H;
                                  dependent destruction H
                    end
        | [ VC: CaptureRange.Valid _ (Some (capture_range ?s ?e)) |- _ ] =>
            dependent destruction VC
        | [ |- CaptureRange.Valid _ _ ] => constructor
        | [ Eq: _ = _ |- _ ] => match type of Eq with
          | Success ?x = Success _ =>
            (check_type x CaptureRange + check_type x (option CaptureRange));
            injection Eq; clear Eq; intros Eq
          | ?s = ?x =>
            is_var s;
            (check_type x CaptureRange + check_type x (option CaptureRange) + check_type x (Result (option CaptureRange) MatchError));
            subst s
          | ?x = ?s =>
            is_var s;
            (check_type x CaptureRange + check_type x (option CaptureRange) + check_type x (Result (option CaptureRange) MatchError));
            subst s
          end
        end).

    Ltac solvers t := lazymatch goal with
    | [ Eq: List.Update.Nat.One.update (Some (capture_range ?s ?e)) ?c _ = Success ?c',
        H: List.Forall.Forall ?c (CaptureRange.Valid ?str)
        |- List.Forall.Forall ?c' _ ] =>
          refine (List.Update.Nat.One.prop_preservation _ _ _ _ _ H _ Eq); constructor; unfold IteratorOn; t
    | [ H: List.Forall.Forall ?oc (CaptureRange.Valid ?str),
        Eq: List.Update.Nat.Batch.update _ ?oc _ = Success ?nc
      |- List.Forall.Forall ?nc (CaptureRange.Valid ?str) ] =>
          refine (List.Update.Nat.Batch.prop_preservation _ _ _ _ _ H _ Eq); solve [ constructor | assumption | t ]
    end.

    Local Ltac solve_impl t := solve [ normalize; (solvers || t) ].

    Ltac solve := solve_impl idtac.
    Ltac solve_with t := solve_impl t.
  End CaptureRange.

  Module MatchState.
    Definition OnInput (str: list Character) (x: MatchState) := MatchState.input x = str.
    Definition Valid (str: list Character) (rer: RegExp) (x: MatchState) :=
      OnInput str x /\
      IteratorOn str (MatchState.endIndex x) /\
      length (MatchState.captures x) = RegExp.capturingGroupsCount rer /\
      List.Forall.Forall (MatchState.captures x) (CaptureRange.Valid str).

    Lemma change_captures: forall str rer input endIndex cap cap',
      length cap' = RegExp.capturingGroupsCount rer ->
      List.Forall.Forall cap' (CaptureRange.Valid str) ->
      Valid str rer (match_state input endIndex cap) ->
      Valid str rer (match_state input endIndex cap').
    Proof.
      intros str rer input endIndex cap cap' H0 H1 [ OI_x [ IO_x V_cap ]]. 
      unfold Valid. split_conjs; try assumption.
    Qed.

    (*  Normalizes all MatchStates by doing the following:
        - Destructing them into their components
        - Then, if the MatchState is known to be on a particular string, eliminate the string introduced at the previous step. *)
    Ltac normalize := repeat
    (   CaptureRange.normalize
    ||  simpl (match_state _ _ _) in *
    ||  simpl (MatchState.input _) in *
    ||  simpl (MatchState.endIndex _) in *
    ||  simpl (MatchState.captures _) in *
    ||  match goal with
        | [ Eq: _ = _ |- _ ] => match type of Eq with
          | Success ?x = Success _ =>
            (check_type x MatchState + check_type x (option MatchState));
            injection Eq; clear Eq; intros Eq
          | ?s = ?x =>
            is_var s;
            (check_type x MatchState + check_type x (option MatchState) + check_type x (Result (option MatchState) MatchError));
            subst s
          | ?x = ?s =>
            is_var s;
            (check_type x MatchState + check_type x (option MatchState) + check_type x (Result (option MatchState) MatchError));
            subst s
          end
        end
    ||  lazymatch goal with
        | [ x: MatchState |- _ ] =>
          let input := fresh "input_" x in
          let endIndex := fresh "endIndex_" x in
          let captures := fresh "captures_" x in
          destruct x as [ input endIndex captures ]
        | [ H: OnInput ?str (match_state ?input _ _) |- _ ] =>
          unfold OnInput in H; cbn in H;
          try rewrite -> H in *; clear H; clear input
        | [ H: MatchState.Valid ?str _ (match_state ?input ?endIndex ?captures) |- _ ] =>
          let OI := fresh "Eq_" input in
          let Iterx := fresh "Iter_" endIndex in
          let VCL := fresh "VCL_" captures in
          let VCF := fresh "VCF_" captures in
          let Tmp := fresh "TMP" in
          destruct H as [ OI [ Iterx [ VCL VCF ]]];
          try rewrite -> Tmp in *
        | [ |- MatchState.Valid _ _ _ ] =>
          unfold Valid; split_conjs

        | [ H: List.Update.Nat.One.update _ _ _ = Success _ |- _ ] =>
          pose proof (List.Update.Nat.One.success_length _ _ _ _ H) as <-
        | [ H: List.Update.Nat.Batch.update _ _ _ = Success _ |- _ ] =>
          pose proof (List.Update.Nat.Batch.success_length _ _ _ _ H) as <-
        end).

    Ltac solvers t := assumption || reflexivity || CaptureRange.solvers t (*|| (Zhelper; apply characterClass_successful_state_Valid; assumption)*).
    (* Solves the current goal by 1. normalizing the states 2. leveraging assumptions and reflexivity *)
    Local Ltac solve_impl t := solve [ normalize; unfold OnInput, Valid; (solvers t || t) ].

    Ltac solve := solve_impl idtac.
    Ltac solve_with t := solve_impl t.


    Definition init (rer: RegExp) (str: list Character) (i: nat) := (match_state str (Z.of_nat i) (List.repeat None (RegExp.capturingGroupsCount rer))).

    Lemma valid_init: forall rer str i, (i <= length str) -> Valid str rer (init rer str i).
    Proof.
      intros rer str i Ineq_i. normalize; try MatchState.solve_with lia.
      - apply List.repeat_length.
      - apply List.Forall.repeat. constructor.
    Qed.
  End MatchState.

  Module Progress.
    Local Ltac hammer :=
      repeat match goal with
      | [ H: progress _ _ (Success (Some _)) |- _ ] => inversion H; clear H; subst
      | [ H: directionalProgress ?d _ _ |- _ ] => is_constructor d; inversion H; clear H
      | [ _: directionalProgress ?d _ _ |- _ ] => destruct d
      | [ |- progress _ _ ?y ] => is_var y; let Eq := fresh "Eq" y in destruct y eqn:Eq
      | [ |- progress _ _ (Success ?y) ] => is_var y; let Eq := fresh "Eq" y in destruct y eqn:Eq
      | [ |- progress ?d _ _ ] => is_constructor d; constructor
      | [ |- progress ?d _ _ ] => destruct d
      | [ |- directionalProgress ?d _ _ ] => is_constructor d; constructor
      | [ |- directionalProgress ?d _ _ ] => destruct d
      end.

    Lemma step: forall x dir n, (0 <= n)%Z -> progress dir x (Success (Some (match_state 
        (MatchState.input x)
        (if Direction.eqb dir forward
         then (MatchState.endIndex x + n)%Z
         else (MatchState.endIndex x - n)%Z) 
        (MatchState.captures x)))).
    Proof. intros. destruct dir; (constructor; cbn in *; solve [ assumption | constructor; cbn; lia ]). Qed.

    Lemma refl: forall dir x, (progress dir) x (Success (Some x)).
    Proof. intros. hammer. 1,3: congruence. all: lia. Qed.

    Lemma trans: forall dir x y z, (progress dir) x (Success (Some y)) -> (progress dir) y z -> (progress dir) x z.
    Proof.
      intros. hammer.
      1,3: congruence.
      all: lia.
    Qed.

    Lemma ignores_captures_r: forall c1 c2 dir x i n,
          (progress dir) x (Success (Some (i [@ n $ c1])))
      <-> (progress dir) x (Success (Some (i [@ n $ c2]))).
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

    Lemma progress_same_input: forall dir x y, progress dir x (Success (Some y))
      -> MatchState.input x = MatchState.input y.
    Proof. intros. inversion H. assumption. Qed.

    (*  Normalize the hypotheses/goals related to progress:
        - Normalize all MatchStates (using MatchState.normalize)
        - Uniformizes all captures, which are irrelevant to progress (replaces all of them by DMap.empty)
        - Derives that two MatchStates have the same input from progress hypotheses *)
    Ltac normalize := repeat (
        MatchState.normalize
    ||  rewrite <- (ignores_captures_l (List.empty)) in *
    ||  rewrite <- (ignores_captures_r (List.empty)) in *
    ||  lazymatch goal with
        | [ H: progress _ (?i [@ _ $ _]) (Success (Some (?i [@ _ $ _]))) |- _ ] => fail
        | [ H: progress _ (?i1 [@ _ $ _]) (Success (Some (?i2 [@ _ $ _]))) |- _ ] =>
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
    Ltac solve := solve [ normalize; solvers ].

    Ltac saturate_step := normalize; match goal with
    | [ H1: progress ?dir ?x (Success (Some ?y)), H2: progress ?dir ?y (Success ?z) |- _ ] =>
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
    Definition HonoresContinuation (str: list Character) (rer: RegExp) (m: Matcher) (dir: direction) := forall x c z,
      (* For any valid state *)
      MatchState.Valid str rer x ->
      (* If the overall computation succeeded *)
      m x c = Success (Some z) ->
      (* There is an intermediate value y that was produced by m and then passed to c which then succeeded. *)
      exists y, MatchState.Valid str rer y /\ progress dir x (Success (Some y)) /\ c y = Success (Some z).
    #[export]
    Hint Unfold HonoresContinuation : Warblre.

    (*  Automated tactic to find the intermediate value 
        It will also try to prove the conditions on the intermediate value.
      *)
    Ltac search := unfold wrap_option,HonoresContinuation in *; subst; lazymatch goal with
    | [ H: Success _ = Success _ |- _ ] => injection H; clear H; intros H; search
    | [ H: ?c ?y = Success ?z |- exists x, MatchState.Valid _ _ _ /\ progress ?dir _ _ /\ ?c x = Success ?z ] =>
      exists y; split_conjs;
      [ assumption + ( unfold MatchState.Valid; split_conjs; try MatchState.solve )
      | try solve [Progress.saturate]
      | apply H ]
    end.

    Lemma repeatMatcher: forall str rer fuel dir m min max greedy parenIndex parenCount,
          HonoresContinuation str rer m dir ->
          HonoresContinuation str rer (fun x c => repeatMatcher' m min max greedy x c parenIndex parenCount fuel) dir.
    Proof.
      (* The 'recursive' case (i.e. when min is not zero or the endIndex is different from last iteration) *)
      assert (forall x z s c str rer fuel dir m min max greedy parenIndex parenCount,
        MatchState.Valid str rer x ->
        List.Update.Nat.Batch.update None (MatchState.captures x) (List.Range.Nat.Bounds.range parenIndex (parenIndex + parenCount)) = Success s ->
        HonoresContinuation str rer m dir ->
        (forall dir m min max greedy parenIndex parenCount,
          HonoresContinuation str rer m dir ->
          HonoresContinuation str rer (Definitions.RepeatMatcher.matcher m min max greedy parenIndex parenCount fuel) dir) ->
        (m (match_state (MatchState.input x) (MatchState.endIndex x) s)
          (Definitions.RepeatMatcher.continuation x c m min max greedy parenIndex parenCount fuel) = Success (Some z)) ->
        exists y : MatchState,
          MatchState.Valid str rer y /\ progress dir x (Success (Some y)) /\ c y = Success (Some z)
      ) as Rec. {
        intros x z s c str rer fuel dir m min max greedy parenIndex parenCount Vx Ex_s HCm IH Eq_rec.
        unfold HonoresContinuation in HCm, IH.
        specialize IH with (1 := HCm).
        focus § _ (_ _ []) _ § remember as d in Eq_rec.
        specialize HCm with (2 := Eq_rec).
        specialize (HCm ltac:(MatchState.solve)) as [ y0 [ Vy0 [ Pxy0 Eq_dy0 ]]].
        rewrite -> Heqd in Eq_dy0. unfold Definitions.RepeatMatcher.continuation in Eq_dy0.
        focus § _ [] _ § auto destruct in Eq_dy0.
        specialize IH with (2 := Eq_dy0).
        specialize IH with (1 := Vy0) as [ y1 [ Vy1 [ Py0y1 Eq_cy1 ]]].
        search.
      }

      induction fuel; [ discriminate | ].
      cbn. intros dir m min max greedy parenIndex parenCount HCm x c z Vx H.
      repeat rewrite Nat.add_sub in *.
      focus § _ [] _ § auto destruct in H.
      - search.
      - eapply Rec; eassumption.
      - search.
      - eapply Rec; eassumption.
      - injection H as [=->].
        eapply Rec; eassumption.
      - search.
    Qed.

    Lemma characterSetMatcher: forall str rer A invert dir,
          HonoresContinuation str rer (characterSetMatcher rer A invert dir) dir.
    Proof.
      intros str rer A invert dir x c z Vx Eq_z.
      unfold characterSetMatcher in Eq_z. focus § _ [] _ § auto destruct in Eq_z.
      boolean_simplifier.
      search.
      - Zhelper. MatchState.normalize. lia.
      - apply Progress.step. lia.
    Qed.

    Lemma backreferenceMatcher: forall str rer n dir,
          HonoresContinuation str rer (backreferenceMatcher rer n dir) dir.
    Proof.
      unfold HonoresContinuation. intros str rer n dir x c z Vx Eq_z.
      unfold backreferenceMatcher in Eq_z. focus § _ [] _ § auto destruct in Eq_z.
      - search.
      - search.
        + destruct dir; MatchState.normalize; cbn in *; lia.
        + apply Progress.step. MatchState.normalize. cbn in *. lia.
    Qed.

    Lemma compileSubPattern: forall r ctx str rer dir m,
      compileSubPattern r ctx rer dir = Success m ->
      HonoresContinuation str rer m dir.
    Proof.
      induction r; intros ctx str rer dir m Eq_m x c z; cbn in Eq_m |- *;
      focus § _ [] _ -> _ § auto destruct.
      - injection Eq_m as <-. intros; search.
      - injection Eq_m as <-. apply characterSetMatcher.
      - injection Eq_m as <-. apply characterSetMatcher.
      - destruct ae.
        + focus § _ [] _ § auto destruct in Eq_m. injection Eq_m as <-.
          apply backreferenceMatcher.
        + destruct esc; focus § _ [] _ § auto destruct in Eq_m; injection Eq_m as <-; apply characterSetMatcher.
        + destruct esc; focus § _ [] _ § auto destruct in Eq_m; injection Eq_m as <-; apply characterSetMatcher.
        + focus § _ [] _ § auto destruct in Eq_m. injection Eq_m as <-.
          apply backreferenceMatcher.
      - focus § _ [] _ § auto destruct in Eq_m. injection Eq_m as <-.
        apply characterSetMatcher.
      - focus § _ [] _ § auto destruct in Eq_m. injection Eq_m as <-.
        intros Vx Eq_z.
        focus § _ [] _ § auto destruct in Eq_z.
        + injection Eq_z as ->. apply IHr1 with (1 := AutoDest_); assumption.
        + apply IHr2 with (1 := AutoDest_0); assumption.
      - focus § _ [] _ § auto destruct in Eq_m. injection Eq_m as <-.
        apply repeatMatcher. apply IHr with (1 := AutoDest_).
      - intros Vx Eq_z.
        unfold HonoresContinuation in IHr1,IHr2.
        focus § _ [] _ § auto destruct in Eq_m; injection Eq_m as <-.
        + specialize IHr1 with (1 := AutoDest_) (2 := Vx) (3 := Eq_z) as [y0 [Vy0 [Pxy0 Eq_y0]]].
          specialize IHr2 with (1 := AutoDest_0) (2 := Vy0) (3 := Eq_y0) as [y1 [Vy1 [Pxy1 Eq_y1]]].
          search.
        + specialize IHr2 with (1 := AutoDest_0) (2 := Vx) (3 := Eq_z) as [y0 [Vy0 [Pxy0 Eq_y0]]].
          specialize IHr1 with (1 := AutoDest_) (2 := Vy0) (3 := Eq_y0) as [y1 [Vy1 [Pxy1 Eq_y1]]].
          search.
      - intros Vx Eq_z.
        unfold HonoresContinuation in IHr.
        focus § _ [] _ § auto destruct in Eq_m; injection Eq_m as <-.
        specialize IHr with (str := str) (1 := AutoDest_) (2 := Vx) (3 := Eq_z) as [y [Vy [Pxy Eq_y]]].
        focus § _ [] _ § auto destruct in Eq_y.
        focus § _ [] _ § auto destruct in AutoDest_1. rewrite -> Nat.add_sub in AutoDest_1.
        search.
        MatchState.normalize.
        refine (List.Update.Nat.One.prop_preservation _ _ _ _ _ VCF_captures_y _ AutoDest_1).
        focus § _ [] _ § auto destruct in AutoDest_0; injection AutoDest_0 as <-; Zhelper; MatchState.normalize; lia.
      - intros Vx Eq_z.
        unfold HonoresContinuation in IHr.
        focus § _ [] _ § auto destruct in Eq_m; injection Eq_m as <-.
        focus § _ [] _ § auto destruct in Eq_z.
        specialize IHr with (1 := AutoDest_) (2 := Vx) (3 := AutoDest_0) as [y [Vy [Pxy Eq_y]]].
        search.
      - intros Vx Eq_z.
        focus § _ [] _ § auto destruct in Eq_m; injection Eq_m as <-.
        focus § _ [] _ § auto destruct in Eq_z.
        search.
      - intros Vx Eq_z.
        unfold HonoresContinuation in IHr.
        focus § _ [] _ § auto destruct in Eq_m; injection Eq_m as <-.
        focus § _ [] _ § auto destruct in Eq_z.
        specialize IHr with (1 := AutoDest_) (2 := Vx) (3 := AutoDest_0) as [y [Vy [Pxy Eq_y]]].
        search.
      - intros Vx Eq_z.
        focus § _ [] _ § auto destruct in Eq_m; injection Eq_m as <-.
        focus § _ [] _ § auto destruct in Eq_z.
        search.
    Qed.
  End IntermediateValue.

  Module Monotony.
    Lemma compilePattern: forall r rer input i m,
      compilePattern r rer = Success m ->
      progress forward (match_state input (Z.of_nat i) (List.repeat None (RegExp.capturingGroupsCount rer))) (m input i).
    Proof.
      intros r rer input i m H.
      unfold compilePattern in *.
      focus § _ [] _ § auto destruct in H. injection H as <-.
      cbn. focus § _ _ _ [] § auto destruct.
      - constructor.
      - boolean_simplifier. spec_reflector PeanoNat.Nat.leb_spec0.
        (* Assert that the start state is valid *)
        focus § _ _ [] _ § do (fun x => assert (MatchState.Valid input rer x) as V_x). {
          constructor.
          + subst. MatchState.solve.
          + subst. split_conjs.
            * subst. cbn. constructor; lia.
            * cbn. rewrite -> List.repeat_length. reflexivity.
            * intros j v Indexed.
              cbn in Indexed. apply List.Indexing.Nat.repeat in Indexed. subst.
              constructor.
        }
        (* Eval program; most cases are trivial since they fail *)
        (focus § _ _ _ [] § do (fun t => destruct t as [ [ z | ] | ] eqn:Eq_z)); try solve[ constructor ].
        (* Use the intermediate value lemma to conclude *)
        pose proof (IntermediateValue.compileSubPattern _ _ _ _ _ _ AutoDest_ _ _ _ V_x Eq_z) as [y [V_y [ P_xy <- ]]].
        constructor.
        + MatchState.solve.
        + dependent destruction P_xy. assumption.
    Qed.
  End Monotony.

  Module Safety.
    Definition SafeMatcher (str: list Character) (rer: RegExp) (m: Matcher) (dir: direction) := forall x c,
      (* For any valid state *)
      MatchState.Valid str rer x ->
      (* If the overall computation runs out of fuel *)
      m x c = match_assertion_failed ->
      (* There is an intermediate value y that was produced by m and then passed to c which then ran out of fuel. *)
      exists y, MatchState.Valid str rer y /\ progress dir x (Success (Some y)) /\ c y = match_assertion_failed.

    Ltac search := lazymatch goal with
    | [ H: Failure _ = match_assertion_failed |- _ ] => try rewrite -> H in *; clear H; search
    | [ H: ?c ?y = match_assertion_failed |- exists x, MatchState.Valid _ _ x /\ progress ?dir _ _ /\ ?c x = match_assertion_failed ] =>
      exists y; split_conjs;
      [ try Progress.solve
      | try solve [Progress.saturate]
      | apply H ]
    end.

    Lemma repeatMatcher: forall dir m min max greedy parenIndex parenCount rer str,
      Captures.Valid rer parenIndex parenCount ->
      SafeMatcher str rer m dir ->
      SafeMatcher str rer (fun x c => repeatMatcher m min max greedy x c parenIndex parenCount) dir.
    Proof.
      assert (Ind: forall fuel dir m min max greedy parenIndex parenCount rer str,
        Captures.Valid rer parenIndex parenCount ->
        SafeMatcher str rer m dir ->
        SafeMatcher str rer (fun x c => repeatMatcher' m min max greedy x c parenIndex parenCount fuel) dir). {
          induction fuel; intros dir m min max greedy parenIndex parenCount rer str V_captures S_m x c V_x Eq_af; cbn in Eq_af; try easy.
          focus § _ [] _ § auto destruct in Eq_af.
          - search.
          - apply S_m in Eq_af as [ y0 [ V_y0 [ P_x_y0 Eq_af ]]]; try MatchState.solve.
            + focus § _ [] _ § auto destruct in Eq_af.
              apply (IHfuel _ _ _ _ greedy parenIndex parenCount _ str V_captures S_m _ c V_y0) in Eq_af as [ y1 [ V_y1 [ P_y0_y1 Eq_af ]]].
              search.
          - apply S_m in Eq_af as [ y0 [ V_y0 [ P_x_y0 Eq_af ]]]; try MatchState.solve.
            focus § _ [] _ § auto destruct in Eq_af.
            apply (IHfuel _ _ _ _ greedy parenIndex parenCount _ str V_captures S_m _ c V_y0) in Eq_af as [ y1 [ V_y1 [ P_y0_y1 Eq_af ]]].
            search.
          - rewrite <- Eq_af. search.
          - search.
          - injection Eq_af as ->.
            apply S_m in AutoDest_3 as [ y0 [ V_y0 [ P_x_y0 Eq_af ]]]; try MatchState.solve.
            focus § _ [] _ § auto destruct in Eq_af.
            apply (IHfuel _ _ _ _ greedy parenIndex parenCount _ str V_captures S_m _ c V_y0) in Eq_af as [ y1 [ V_y1 [ P_y0_y1 Eq_af ]]].
            search.
          - injection Eq_af as ->.
            apply List.Update.Nat.Batch.failure_bounds in AutoDest_0. unfold Captures.Valid in V_captures.
            destruct V_x as [ _ [ _ [ VCL_x _ ]]]. rewrite -> VCL_x in *. repeat rewrite Nat.add_sub in *. contradiction.
      }
      intros dir m min max greedy parenIndex parenCount rer str H H0 x c H1 H2. specialize Ind with (1 := H) (2 := H0).
      unfold repeatMatcher. unfold SafeMatcher in Ind.
      apply Ind with (1 := H1) (2 := H2).
    Qed.

    Lemma characterSetMatcher: forall str rer A invert dir,
      SafeMatcher str rer (characterSetMatcher rer A invert dir) dir.
    Proof.
      intros str rer A invert dir x c Vx Eq_oof.
      unfold characterSetMatcher in Eq_oof. focus § _ [] _ § auto destruct in Eq_oof; hypotheses_reflector.
      - search.
        + Zhelper. MatchState.solve_with lia.
        + apply Progress.step. lia.
      - injection Eq_oof as <-. unfold CharSet.exist in AutoDest_2. apply List.Exists.failure_kind in AutoDest_2 as [_ [ c' [ _ Can_failure ]]].
        rewrite_canonicalize. discriminate.
      - rewrite_canonicalize. discriminate.
      - injection Eq_oof as ->. boolean_simplifier. Zhelper.
        destruct Vx as [ Eq_str [ [ ? ? ] _ ]].
        destruct dir.
        + assert (Z.min (MatchState.endIndex x) (MatchState.endIndex x + 1) = MatchState.endIndex x)%Z as Tmp by lia.
          rewrite -> Tmp in *; clear Tmp.
          apply List.Indexing.Int.failure_bounds in AutoDest_0 as [ ? | ? ]; lia.
        + assert (Z.min (MatchState.endIndex x) (MatchState.endIndex x - 1) = MatchState.endIndex x - 1)%Z as Tmp by lia.
          rewrite -> Tmp in *; clear Tmp.
          rewrite -> Eq_str in *.
          apply List.Indexing.Int.failure_bounds in AutoDest_0 as [ ? | ? ]; try lia.
    Qed.

    Lemma positiveLookaroundMatcher: forall m str rer dir dir',
      IntermediateValue.HonoresContinuation str rer m dir' ->
      SafeMatcher str rer m dir' ->
      SafeMatcher str rer (Definitions.PositiveLookaround.matcher m) dir.
    Proof.
      intros m str rer dir dir' HC_m S_m. intros x c V_x Eq_af.
      unfold Definitions.PositiveLookaround.matcher in *.
      focus § _ [] _ § auto destruct in Eq_af.
      + specialize (HC_m _ _ _ V_x AutoDest_) as [ y0 [ V_y0 [ P_x_y0 Eq_y0 ]]].
        search.
      + injection Eq_af as ->.
        specialize (S_m _ _ V_x AutoDest_) as [ y0 [ V_y0 [ P_x_y0 Eq_y0 ]]].
        discriminate.
    Qed.

    Lemma negativeLookaroundMatcher: forall m str rer dir dir',
      SafeMatcher str rer m dir' ->
      SafeMatcher str rer (Definitions.NegativeLookaround.matcher m) dir.
    Proof.
      intros m str rer dir dir' S_m. intros x c V_x Eq_af.
      unfold Definitions.NegativeLookaround.matcher in *.
      focus § _ [] _ § auto destruct in Eq_af.
      + search.
      + injection Eq_af as ->.
        specialize (S_m _ _ V_x AutoDest_) as [ y0 [ V_y0 [ P_x_y0 Eq_y0 ]]].
        discriminate.
    Qed.

    Lemma backreferenceMatcher: forall str rer n dir,
      (positive_to_non_neg n) <= RegExp.capturingGroupsCount rer ->
      SafeMatcher str rer (backreferenceMatcher rer n dir) dir.
    Proof.
      intros str rer n dir Bound_n x c Vx Eq_af.
      unfold backreferenceMatcher in Eq_af. focus § _ [] _ § auto destruct in Eq_af.
      - search.
      - search.
        + destruct dir; cbn in *; MatchState.solve_with ltac:(cbn in *; lia).
        + apply Progress.step. MatchState.normalize. cbn in *. lia.
      - injection Eq_af as ->. Zhelper.
        apply List.Exists.failure_kind in AutoDest_3.
        destruct AutoDest_3 as [ i [ j [ Eq_indexed Eq_af ]]].
        pose proof Eq_indexed as Tmp. apply List.Range.Int.Bounds.indexing in Tmp as ->.
        apply List.Indexing.Int.success_bounds in Eq_indexed as Bounds_i. clear Eq_indexed.
        destruct Vx as [ Eq_str [ [ ? ? ] [ _ V_t ]]].
        cbn in AutoDest_. focus § _ [] _ § auto destruct in AutoDest_.
        specialize (V_t _ _ AutoDest_). dependent destruction V_t.
        rename s into t_s, e into t_e, H into Ineq_t, H0 into IO_t_s, H1 into IO_t_e.
        MatchState.normalize. cbn in *. rewrite -> List.Range.Int.Bounds.length in *.
        focus § _ [] _ § auto destruct in Eq_af; injection Eq_af as ->.
        + rewrite_canonicalize. discriminate.
        + destruct dir.
          * apply List.Indexing.Int.failure_bounds in AutoDest_2 as [ ? | ? ]; lia.
          * apply List.Indexing.Int.failure_bounds in AutoDest_2 as [ ? | ? ]; lia.
        + rewrite_canonicalize. discriminate.
        + destruct dir.
          * apply List.Indexing.Int.failure_bounds in AutoDest_0 as [ ? | ? ]; lia.
          * apply List.Indexing.Int.failure_bounds in AutoDest_0 as [ ? | ? ]; lia.
      - injection Eq_af as ->.
        cbn in AutoDest_. focus § _ [] _ § auto destruct in AutoDest_.
        apply List.Indexing.Nat.failure_bounds in AutoDest_.
        destruct Vx as [ _ [ _ [ Tmp _ ]]]; rewrite -> Tmp in *; clear Tmp.
        pose proof (NonNegInt.pos n). lia.
    Qed.

    Lemma compileSubPattern: forall rer root r ctx dir str m,
      countLeftCapturingParensWithin root nil = RegExp.capturingGroupsCount rer ->
      Root root r ctx ->
      EarlyErrors.Pass.Regex root nil ->
      compileSubPattern r ctx rer dir = Success m ->
      SafeMatcher str rer m dir.
    Proof.
      intros rer root.
      induction r; cbn; intros ctx dir str m Eq_rer R_r GR_root Eq_m.
      - focus § _ [] _ § auto destruct in Eq_m; injection Eq_m as <-.
        intros x c Vx Sc. search.
      - focus § _ [] _ § auto destruct in Eq_m; injection Eq_m as <-.
        apply characterSetMatcher.
      - focus § _ [] _ § auto destruct in Eq_m; injection Eq_m as <-.
        apply characterSetMatcher.
      - destruct ae.
        + focus § _ [] _ § auto destruct in Eq_m; injection Eq_m as <-.
          apply backreferenceMatcher. boolean_simplifier. spec_reflector Nat.leb_spec0. assumption.
        + destruct esc; focus § _ [] _ § auto destruct in Eq_m; injection Eq_m as <-; apply characterSetMatcher.
        + destruct esc; focus § _ [] _ § auto destruct in Eq_m; injection Eq_m as <-; apply characterSetMatcher.
        + focus § _ [] _ § auto destruct in Eq_m; injection Eq_m as <-.
          apply backreferenceMatcher. boolean_simplifier. cbn in *.
          apply List.Unique.success in AutoDest_0. destruct s. cbn in *.
          assert (List.Indexing.Nat.indexing (groupSpecifiersThatMatch (AtomEsc (AtomEscape.GroupEsc id)) ctx id) 0 = Success (r, l)) as Eq_indexed. {
            rewrite -> AutoDest_0. reflexivity.
          }
          pose proof (EarlyErrors.groupSpecifiersThatMatch_is_filter_map (AtomEsc (AtomEscape.GroupEsc id)) ctx id) as (f & _ & Def_f).
          apply Def_f in Eq_indexed. destruct Eq_indexed as (ctx' & ? & Eq_indexed).
          subst. destruct (countLeftCapturingParensBefore_impl ctx' + 1) eqn:Eq; try lia. cbn in *.
          apply Zip.Walk.soundness in Eq_indexed. eapply Zip.Down.same_root_down in Eq_indexed; [ | eapply R_r ]. cbn in *.
          pose proof (EarlyErrors.countLeftCapturingParensBefore_contextualized _ _ _ Eq_indexed GR_root).
          subst. unfold countLeftCapturingParensBefore,countLeftCapturingParensWithin in *. cbn in *.
          apply NonNegInt.to_positive_soundness in AutoDest_1.
          lia.
      - focus § _ [] _ § auto destruct in Eq_m; injection Eq_m as <-.
        apply characterSetMatcher.
      - intros x c Vx Sc.
        focus § _ [] _ § auto destruct in Eq_m; injection Eq_m as <-.
        focus § _ [] _ § auto destruct in Sc.
        + specialize (IHr2 (Disjunction_right r1 :: ctx) _ str _ ltac:(eassumption) ltac:(eassumption) ltac:(eassumption) ltac:(eassumption) x c ltac:(eassumption) ltac:(eassumption)) as [ ? [ ? [ ? ? ]]].
          search.
        + injection Sc as ->.
          specialize (IHr1 (Disjunction_left r2 :: ctx) _ str _ ltac:(eassumption) ltac:(eassumption) ltac:(eassumption) ltac:(eassumption) x c ltac:(eassumption) ltac:(eassumption)) as [ ? [ ? [ ? ? ]]].
          search.
      - focus § _ [] _ § auto destruct in Eq_m; injection Eq_m as <-.
        apply repeatMatcher.
        + intros i v Eq_indexed.
          pose proof (List.Indexing.Nat.success_bounds _ _ _ Eq_indexed). rewrite -> List.Range.Nat.Bounds.length in *.
          apply List.Range.Nat.Bounds.indexing in Eq_indexed.
          pose proof (EarlyErrors.countLeftCapturingParensBefore_contextualized _ _ _ R_r GR_root).
          unfold countLeftCapturingParensBefore,countLeftCapturingParensWithin in *. cbn in *. lia.
        + apply (IHr (Quantified_inner q :: ctx) _ _ _ ltac:(eassumption) ltac:(eassumption) ltac:(eassumption) ltac:(eassumption)).
      - intros x c V_x S_c.
        focus § _ [] _ § auto destruct in Eq_m; injection Eq_m as <-.
        + specialize (IHr1 _ _ _ _ ltac:(eassumption) ltac:(eapply Zip.Down.same_root_down0; [ constructor | eassumption]) ltac:(eassumption) ltac:(eassumption) _ _ V_x S_c) as [ y0 [ V_y0 [ P_x_y0 Eq_y0 ]]].
          specialize (IHr2 _ _ _ _ ltac:(eassumption) ltac:(eapply Zip.Down.same_root_down0; [ constructor | eassumption]) ltac:(eassumption) ltac:(eassumption) _ _ V_y0 Eq_y0) as [ y1 [ V_y1 [ P_x_y1 Eq_y1 ]]].
          search.
        + specialize (IHr2 _ _ _ _ ltac:(eassumption) ltac:(eapply Zip.Down.same_root_down0; [ constructor | eassumption]) ltac:(eassumption) ltac:(eassumption) _ _ V_x S_c) as [ y0 [ V_y0 [ P_x_y0 Eq_y0 ]]].
          specialize (IHr1 _ _ _ _ ltac:(eassumption) ltac:(eapply Zip.Down.same_root_down0; [ constructor | eassumption]) ltac:(eassumption) ltac:(eassumption) _ _ V_y0 Eq_y0) as [ y1 [ V_y1 [ P_x_y1 Eq_y1 ]]].
          search.
      - intros x c V_x Eq_af.
        focus § _ [] _ § auto destruct in Eq_m; injection Eq_m as <-.
        specialize (IHr _ _ _ _ ltac:(eassumption) ltac:(eapply Zip.Down.same_root_down0; [ constructor | eassumption]) ltac:(eassumption) ltac:(eassumption) _ _ V_x Eq_af) as [ y0 [ V_y0 [ P_x_y0 Eq_y0 ]]].
        focus § _ [] _ § auto destruct in Eq_y0.
        + focus § _ [] _ § auto destruct in AutoDest_0; focus § _ [] _ § auto destruct in AutoDest_1; rewrite -> Nat.add_sub in AutoDest_1.
          * search. MatchState.solve_with lia.
          * search. MatchState.solve_with lia.
        + injection Eq_y0 as ->.
          focus § _ [] _ § auto destruct in AutoDest_1.
          * spec_reflector Nat.eqb_spec. lia.
          * rewrite -> Nat.add_sub in *.
            apply List.Update.Nat.One.failure_bounds in AutoDest_1.
            pose proof (EarlyErrors.countLeftCapturingParensBefore_contextualized _ _ _ R_r GR_root).
            unfold countLeftCapturingParensBefore,countLeftCapturingParensWithin in *. cbn in *. MatchState.solve_with lia.
        + injection Eq_y0 as ->.
          focus § _ [] _ § auto destruct in AutoDest_0; destruct dir; try discriminate.
          * Zhelper. MatchState.normalize.
            dependent destruction P_x_y0.
            dependent destruction H0. cbn in *.
            lia.
          * Zhelper.
            dependent destruction P_x_y0.
            dependent destruction H0. cbn in *.
            lia.
      - focus § _ [] _ § auto destruct in Eq_m; injection Eq_m as <-.
        apply positiveLookaroundMatcher with (dir' := forward).
        + apply IntermediateValue.compileSubPattern with (1 := AutoDest_).
        + apply (IHr (Lookahead_inner :: ctx) _ _ _ ltac:(eassumption) ltac:(eassumption) ltac:(eassumption) ltac:(eassumption)).
      - focus § _ [] _ § auto destruct in Eq_m; injection Eq_m as <-.
        apply negativeLookaroundMatcher with (dir' := forward).
        apply (IHr (NegativeLookahead_inner :: ctx) _ _ _ ltac:(eassumption) ltac:(eassumption) ltac:(eassumption) ltac:(eassumption)).
      - focus § _ [] _ § auto destruct in Eq_m; injection Eq_m as <-.
        apply positiveLookaroundMatcher with (dir' := backward).
        + apply IntermediateValue.compileSubPattern with (1 := AutoDest_).
        + apply (IHr (Lookbehind_inner :: ctx) _ _ _ ltac:(eassumption) ltac:(eassumption) ltac:(eassumption) ltac:(eassumption)).
      - focus § _ [] _ § auto destruct in Eq_m; injection Eq_m as <-.
        apply negativeLookaroundMatcher with (dir' := backward).
        eapply (IHr (NegativeLookbehind_inner :: ctx) _ _ _ ltac:(eassumption) ltac:(eassumption) ltac:(eassumption) ltac:(eassumption)).
    Qed.

    Theorem compilePattern: forall r rer input i m,
      EarlyErrors.Pass.Regex r nil ->
      countLeftCapturingParensWithin r nil = RegExp.capturingGroupsCount rer ->
      0 <= i <= (length input) ->
      compilePattern r rer = Success m ->
      m input i <> match_assertion_failed.
    Proof.
      intros r rer input i m GR Eq_rer Bounds_i Eq_m. unfold compilePattern in Eq_m. 
      focus § _ [] _ § auto destruct in Eq_m. injection Eq_m as <-.
      focus § _ (_ [] _) § auto destruct.
      - hypotheses_reflector. spec_reflector Nat.leb_spec0. contradiction.
      - remember (match_state input i (List.repeat None (RegExp.capturingGroupsCount rer))) as x eqn:Eq_x.
        pose proof (Safety.compileSubPattern _ _ _ nil forward input _ Eq_rer (Root.id _) GR AutoDest_ x (fun y => y)) as Falsum.
        assert (MatchState.Valid input rer x) as V_x. {
          subst x. apply MatchState.valid_init. lia.
        }
        focus § _ (_ [] _) § do (fun t => destruct t as [ | f ]; try easy; destruct f; try easy).
        fforward Falsum. destruct Falsum as [ ? [ _ [ _ ? ]]].
        subst. discriminate.
    Qed.
  End Safety.

  Module Termination.
    Definition TerminatingMatcher (str: list Character) (rer: RegExp) (m: Matcher) (dir: direction) := forall x c,
      (* For any valid state *)
      MatchState.Valid str rer x ->
      (* If the overall computation runs out of fuel *)
      m x c = out_of_fuel ->
      (* There is an intermediate value y that was produced by m and then passed to c which then ran out of fuel. *)
      exists y, MatchState.Valid str rer y /\ progress dir x (Success (Some y)) /\ c y = out_of_fuel.

    Definition remainingChars (x: MatchState) (dir: direction): nat := match dir with
    | forward => length (MatchState.input x) - Z.to_nat (MatchState.endIndex x)
    | backward => Z.to_nat (MatchState.endIndex x)
    end.
    Definition fuelBound (min: non_neg_integer) (x: MatchState) (dir: direction) := min + (remainingChars x dir)  + 1.

    Lemma repeatMatcherFuel_satisfies_bound: forall min x str rer dir, MatchState.Valid str rer x -> fuelBound min x dir <= repeatMatcherFuel min x.
    Proof. intros. unfold fuelBound,repeatMatcherFuel in *. destruct H as [ <- [ [ Bounds_Ei_x_low Bounds_Ei_x_high ] VC_x ] ]. destruct dir; cbn; lia. Qed.

    Lemma fuelDecreases_min: forall dir min min' x x' b,
      min' < min -> progress dir x (Success (Some x')) -> fuelBound min x dir <= S b -> fuelBound min' x' dir <= b.
    Proof.
      intros. unfold fuelBound,remainingChars in *. inversion H0; destruct dir; inversion H6; subst.
      - rewrite -> H3 in *. lia.
      - lia.
    Qed.

    Lemma fuelDecreases_progress: forall dir str rer min x x' b,
      progress dir x (Success (Some x')) ->
      ((MatchState.endIndex x) =? (MatchState.endIndex x'))%Z = false ->
      MatchState.Valid str rer x ->
      MatchState.Valid str rer x' ->
      fuelBound min x dir <= S b ->
      fuelBound min x' dir <= b.
    Proof.
      intros dir str rer min x x' b P_x_x' Neq_Eis [ <- [ [ Bei_x_l Bei_x_h ] VC_x ] ] [ <- [ [ B_Ei_x'_l B_Ei_x'_h ] VC_x' ] ] Ineq_fuel.
      dependent destruction P_x_x'. rename H into Eq_inp_x_x', H0 into Dp_x_x'.
      unfold fuelBound, remainingChars in *.
      rewrite <- Eq_inp_x_x' in *.
      spec_reflector Z.eqb_spec.
      dependent destruction Dp_x_x'; lia.
    Qed.

    Ltac search := lazymatch goal with
    | [ H: Failure _ = out_of_fuel |- _ ] => try rewrite -> H in *; clear H; search
    | [ H: ?c ?y = out_of_fuel |- exists x, MatchState.Valid _ _ x /\ progress ?dir _ _ /\ ?c x = out_of_fuel ] =>
      exists y; split; [ | split ];
      [ try Progress.solve
      | try solve [Progress.saturate]
      | apply H ]
    end.

    Lemma repeatMatcher': forall fuel m min max greedy parenIndex parenCount x c dir str rer,
      fuelBound min x dir <= fuel ->
      MatchState.Valid str rer x ->
      TerminatingMatcher str rer m dir ->
      repeatMatcher' m min max greedy x c parenIndex parenCount fuel = out_of_fuel ->
      exists y,
        MatchState.Valid str rer y /\ progress dir x (Success (Some y)) /\ c y = out_of_fuel.
    Proof.
      (* The 'recursive' case (i.e. when min is not zero or the endIndex is different from last iteration) *)
  (*     assert (forall x s c str fuel dir m min max greedy groups,
        MatchState.Valid str x ->
        List.Updating.batch_updating (MatchState.captures x) groups None = Success s ->
        TerminatingMatcher str m dir ->
        (forall dir m min max greedy groups,
          TerminatingMatcher str m dir ->
          TerminatingMatcher str (Definitions.RepeatMatcher.matcher m min max greedy groups fuel) dir) ->
        (m (match_state (MatchState.input x) (MatchState.endIndex x) s)
          (Definitions.RepeatMatcher.continuation x c m min max greedy groups fuel) = out_of_fuel) ->
        exists y : MatchState,
          MatchState.Valid str y /\ progress dir x (Success (Some y)) /\ c y = out_of_fuel
      ) as Rec. {
        intros x s c str fuel dir m min max greedy groups V_x Eq_s Tm IH Eq_rec.
        apply Tm in Eq_rec; try Progress.solve. destruct Eq_rec as [ y [ Vy [ P_x_y Eq_rec ] ] ].
        (focus § _ [] _ § auto destruct in Eq_rec). boolean_simplifier.
        destruct (PeanoNat.Nat.eq_dec min 0).
        - assert(FD: fuelBound 0 y dir <= fuel). {
            (focus § _ [] _ § do (fun t => apply fuelDecreases_progress with (str := str) (x := t)) in P_x_y); try Progress.solve.
            MatchState.normalize. spec_reflector Z.eqb_spec. congruence.
          }
          admit.
        - assert(FD: fuelBound (min - 1) y dir <= fuel). {
            apply fuelDecreases_min with (min := min) (x := x); try Progress.solve.
            + lia.
            + admit.
          }
          admit.
          (* specialize IH with (1 := FD) (2 := Vy) (3 := Tm) (4 := Eq_rec). clear Eq_rec.
          destruct IH as [ z [ Vz [ Pyz Falsum ] ] ].
          search. *)
        
        (*unfold TerminatingMatcher in Tm, IH.
        specialize IH with (1 := Tm).
        focus § _ (_ _ []) _ § remember as d in Eq_rec.
        specialize HCm with (2 := Eq_rec).
        fforward HCm as [ y0 [ Vy0 [ Pxy0 Eq_dy0 ]] ] by MatchState.solve.
        rewrite -> Heqd in Eq_dy0. unfold Definitions.RepeatMatcher.continuation in Eq_dy0.
        focus § _ [] _ § auto destruct in Eq_dy0.
        specialize IH with (2 := Eq_dy0). fforward IH as [ y1 [ Vy1 [ Py0y1 Eq_cy1 ]]].
        search.*)
      } *)
    
      induction fuel; intros m min max greedy parenIndex parenCount x c dir str rer Ineq_fuel Vx Tm Falsum.
      - clear -Ineq_fuel. unfold fuelBound, remainingChars in *. lia.
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
        + apply Tm in Falsum; try Progress.solve. destruct Falsum as [ y [ Vy [ Pxy Falsum ] ] ].
          (focus § _ [] _ § auto destruct in Falsum).
          boolean_simplifier. spec_reflector Nat.eqb_spec. subst.
          assert(FD: fuelBound 0 y dir <= fuel). {
            (focus § _ [] _ § do (fun t => apply fuelDecreases_progress with (str := str) (rer := rer) (x := t)) in Pxy); try Progress.solve.
            MatchState.normalize. spec_reflector Z.eqb_spec. congruence.
          }
          specialize IHfuel with (1 := FD) (2 := Vy) (3 := Tm) (4 := Falsum). clear Falsum.
          destruct IHfuel as [ z [ Vz [ Pyz Falsum ] ] ].
          search.
        + search.
        + search.
        + rewrite -> Falsum in *. clear Falsum. apply Tm in AutoDest_3; try Progress.solve. destruct AutoDest_3 as [ y [ Vy [ Pxy Falsum ] ] ].
          (focus § _ [] _ § auto destruct in Falsum).
          boolean_simplifier. spec_reflector Nat.eqb_spec. subst.
          assert(FD: fuelBound 0 y dir <= fuel). {
            (focus § _ [] _ § do (fun t => apply fuelDecreases_progress with (str := str) (rer := rer) (x := t)) in Pxy); try Progress.solve.
            MatchState.normalize. spec_reflector Z.eqb_spec. congruence.
          }
          specialize IHfuel with (1 := FD) (2 := Vy) (3 := Tm) (4 := Falsum). clear Falsum.
          destruct IHfuel as [ z [ Vz [ Pyz Falsum ] ] ].
          search.
        + injection Falsum as ->.
          apply List.Update.Nat.Batch.failure_is_assertion in AutoDest_0.
          discriminate.
    Qed.

    Lemma repeatMatcher: forall m min max greedy parenIndex parenCount str rer dir,
      TerminatingMatcher str rer m dir ->
      TerminatingMatcher str rer (fun x c => repeatMatcher m min max greedy x c parenIndex parenCount) dir.
    Proof.
      unfold Semantics.repeatMatcher, TerminatingMatcher. intros m min max greedy parenIndex parenCount str rer dir Tm x c V_x Eq_oof.
      apply repeatMatcher' with (4 := Eq_oof); try easy.
      apply repeatMatcherFuel_satisfies_bound with (str := str) (rer := rer).
      assumption.
    Qed.

    Lemma characterSetMatcher: forall str rer A invert dir,
      TerminatingMatcher str rer (characterSetMatcher rer A invert dir) dir.
    Proof.
      intros str rer A invert dir x c Vx Eq_oof.
      unfold characterSetMatcher in Eq_oof. focus § _ [] _ § auto destruct in Eq_oof.
      - search.
        + Zhelper. MatchState.solve_with lia.
        + apply Progress.step. lia.
      - injection Eq_oof as ->.
        unfold CharSet.exist in AutoDest_2. apply List.Exists.failure_kind in AutoDest_2 as [ i [ v [ ? ? ]]].
        rewrite_canonicalize. discriminate.
      - injection Eq_oof as ->. rewrite_canonicalize. discriminate.
      - injection Eq_oof as ->.
        pose proof (@List.Indexing.Int.failure_kind Character) as Falsum. specialize Falsum  with (1 := AutoDest_0).
        cbn in *. congruence.
    Qed.

    Lemma positiveLookaroundMatcher: forall m str rer dir dir',
      IntermediateValue.HonoresContinuation str rer m dir' ->
      TerminatingMatcher str rer m dir' ->
      TerminatingMatcher str rer (Definitions.PositiveLookaround.matcher m) dir.
    Proof.
      intros m str rer dir dir' HC_m S_m. intros x c V_x Eq_oof.
      unfold Definitions.PositiveLookaround.matcher in *.
      focus § _ [] _ § auto destruct in Eq_oof.
      + specialize (HC_m _ _ _ V_x AutoDest_) as [ y0 [ V_y0 [ P_x_y0 Eq_y0 ]]].
        search.
      + injection Eq_oof as ->.
        specialize (S_m _ _ V_x AutoDest_) as [ y0 [ V_y0 [ P_x_y0 Eq_y0 ]]].
        discriminate.
    Qed.

    Lemma negativeLookaroundMatcher: forall m str rer dir dir',
      TerminatingMatcher str rer m dir' ->
      TerminatingMatcher str rer (Definitions.NegativeLookaround.matcher m) dir.
    Proof.
      intros m str rer dir dir' S_m. intros x c V_x Eq_oof.
      unfold Definitions.NegativeLookaround.matcher in *.
      focus § _ [] _ § auto destruct in Eq_oof.
      + search.
      + injection Eq_oof as ->.
        specialize (S_m _ _ V_x AutoDest_) as [ y0 [ V_y0 [ P_x_y0 Eq_y0 ]]].
        discriminate.
    Qed.

    Lemma backreferenceMatcher: forall str rer n dir,
      TerminatingMatcher str rer (backreferenceMatcher rer n dir) dir.
    Proof.
      unfold TerminatingMatcher. intros str rer n dir x c Vx Eq_oof.
      unfold backreferenceMatcher in Eq_oof. focus § _ [] _ § auto destruct in Eq_oof.
      - search.
      - search.
        + destruct dir; cbn in *; MatchState.solve_with ltac:(cbn in *; lia).
        + apply Progress.step. MatchState.normalize. cbn in *. lia.
      - injection Eq_oof as ->.
        apply List.Exists.failure_kind in AutoDest_3.
        destruct AutoDest_3 as [ i [ j [ Eq_indexed Eq_oof ]]].
        focus § _ [] _ § auto destruct in Eq_oof; injection Eq_oof as ->.
        + rewrite_canonicalize. discriminate.
        + pose proof (@List.Indexing.Int.failure_kind Character) as Falsum. specialize Falsum  with (1 := AutoDest_5).
          cbn in *. congruence.
        + rewrite_canonicalize. discriminate.
        + pose proof (@List.Indexing.Int.failure_kind Character) as Falsum. specialize Falsum  with (1 := AutoDest_3).
          cbn in *. congruence.
      - injection Eq_oof as ->.
        pose proof @List.Indexing.Nat.failure_kind as Falsum.
        cbn in AutoDest_. focus § _ [] _ § auto destruct in AutoDest_.
        specialize Falsum  with (1 := AutoDest_).
        cbn in *. congruence.
    Qed.

    Lemma compileSubPattern: forall r ctx rer dir str m,
      compileSubPattern r ctx rer dir = Success m ->
      TerminatingMatcher str rer m dir.
    Proof.
      induction r; intros ctx rer dir str m Eq_m; cbn -[Semantics.repeatMatcher] in Eq_m;
      focus § _ [] _ § auto destruct.
      - focus § _ [] _ § auto destruct in Eq_m; injection Eq_m as <-.
        intros x c Vx H. search.
      - focus § _ [] _ § auto destruct in Eq_m; injection Eq_m as <-.
        apply characterSetMatcher.
      - focus § _ [] _ § auto destruct in Eq_m; injection Eq_m as <-.
        apply characterSetMatcher.
      - destruct ae.
        + focus § _ [] _ § auto destruct in Eq_m; injection Eq_m as <-.
          apply backreferenceMatcher.
        + destruct esc; focus § _ [] _ § auto destruct in Eq_m; injection Eq_m as <-; apply characterSetMatcher.
        + destruct esc; focus § _ [] _ § auto destruct in Eq_m; injection Eq_m as <-; apply characterSetMatcher.
        + focus § _ [] _ § auto destruct in Eq_m; injection Eq_m as <-.
          apply backreferenceMatcher.
      - focus § _ [] _ § auto destruct in Eq_m; injection Eq_m as <-.
        apply characterSetMatcher.
      - intros x c Vx H. unfold TerminatingMatcher in IHr1,IHr2.
        focus § _ [] _ § auto destruct in Eq_m; injection Eq_m as <-.
        focus § _ [] _ § auto destruct in H.
        + specialize IHr2 with (1 := AutoDest_0) (2 := Vx) (3 := H) as [ y0 [ Vy0 [ P_x_y0 Eq_oof0 ]]]. search.
        + injection H as ->. specialize IHr1 with (1 := AutoDest_) (2 := Vx) (3 := AutoDest_1) as [ y0 [ Vy0 [ P_x_y0 Eq_oof0 ]]]. search.
      - focus § _ [] _ § auto destruct in Eq_m; injection Eq_m as <-.
        apply repeatMatcher. apply IHr with (1 := AutoDest_).
      - intros x c Vx H. unfold TerminatingMatcher in IHr1,IHr2.
        focus § _ [] _ § auto destruct in Eq_m; injection Eq_m as <-.
        + specialize IHr1 with (1 := AutoDest_) (2 := Vx) (3 := H) as [ y0 [ Vy0 [ P_x_y0 Eq_oof0 ]]].
          specialize IHr2 with (1 := AutoDest_0) (2 := Vy0) (3 := Eq_oof0) as [ y1 [ Vy1 [ P_x_y1 Eq_oof1 ]]].
          search.
        + specialize IHr2 with (1 := AutoDest_0) (2 := Vx) (3 := H) as [ y0 [ Vy0 [ P_x_y0 Eq_oof0 ]]].
          specialize IHr1 with (1 := AutoDest_) (2 := Vy0) (3 := Eq_oof0) as [ y1 [ Vy1 [ P_x_y1 Eq_oof1 ]]].
          search.
      - intros x c Vx H. unfold TerminatingMatcher in IHr.
        focus § _ [] _ § auto destruct in Eq_m; injection Eq_m as <-.
        specialize IHr with (str := str) (1 := AutoDest_) (2 := Vx) (3 := H) as [ y [ Vy [ P_x_y Eq_oof ]]].
        focus § _ [] _ § auto destruct in Eq_oof.
        + search.
          focus § _ [] _ § auto destruct in AutoDest_1.
          MatchState.normalize; try MatchState.solve.
          apply List.Update.Nat.One.prop_preservation with (3 := AutoDest_1); try assumption.
          focus § _ [] _ § auto destruct in AutoDest_0; injection AutoDest_0 as <-; constructor; solve [ assumption | lia ].
        + focus § _ [] _ § auto destruct in AutoDest_1.
          * spec_reflector Nat.eqb_spec. lia.
          * rewrite -> List.Update.Nat.One.failure_kind with (f := f) in AutoDest_1 by assumption.
            injection AutoDest_1 as <-. discriminate.
        + focus § _ [] _ § auto destruct in AutoDest_0.
          * injection AutoDest_0 as <-. discriminate.
          * injection AutoDest_0 as <-. discriminate.
      - focus § _ [] _ § auto destruct in Eq_m; injection Eq_m as <-.
        apply positiveLookaroundMatcher with (dir' := forward).
        + apply IntermediateValue.compileSubPattern with (1 := AutoDest_).
        + apply IHr with (1 := AutoDest_).
      - focus § _ [] _ § auto destruct in Eq_m; injection Eq_m as <-.
        apply negativeLookaroundMatcher with (dir' := forward). apply IHr with (1 := AutoDest_).
      - focus § _ [] _ § auto destruct in Eq_m; injection Eq_m as <-.
        apply positiveLookaroundMatcher with (dir' := backward).
        + apply IntermediateValue.compileSubPattern with (1 := AutoDest_).
        + apply IHr with (1 := AutoDest_).
      - focus § _ [] _ § auto destruct in Eq_m; injection Eq_m as <-.
        apply negativeLookaroundMatcher with (dir' := backward). apply IHr with (1 := AutoDest_).
    Qed.

    Lemma compilePattern: forall r rer input i m,
      compilePattern r rer = Success m ->
      m input i <> out_of_fuel.
    Proof.
      intros r rer input i m Eq_m. unfold compilePattern in Eq_m.
      focus § _ [] _ § auto destruct in Eq_m. injection Eq_m as <-.
      focus § _ (_ [] _) § auto destruct. boolean_simplifier. spec_reflector Nat.leb_spec0.
      remember (match_state input i (List.repeat None (RegExp.capturingGroupsCount rer))) as x eqn:Eq_x.
      pose proof (compileSubPattern _ _ _ forward input _ AutoDest_ x (fun y => y)) as Falsum.
      assert (MatchState.Valid input rer x) as V_x. {
        subst x. apply MatchState.valid_init. lia.
      }
      focus § _ (_ [] _) § do (fun t => destruct t as [ | f ]; try easy; destruct f; try easy).
      fforward Falsum. destruct Falsum as [ ? [ _ [ _ ? ]]].
      subst. discriminate.
    Qed.

    (*From Coq Require Import Logic.FunctionalExtensionality.
    Definition TerminatingContinuation (c: MatcherContinuation) :=
      forall x, c x <> out_of_fuel.
    Lemma repeatMatcher_fuelWeakening: forall fuelL fuelH (m: Matcher) min max greedy captures x c dir str, fuelL <= fuelH ->
      TerminatingMatcher str m dir -> IntermediateValue.HonoresContinuation str m dir -> TerminatingContinuation c ->
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
      - (focus § _ (_ [] _) § do (fun t => destruct t eqn:Eq in Tl) in Tl).
        + admit.
        + admit.
      - admit.
      - admit.
    Abort.*)
  End Termination.
End Correctness.
