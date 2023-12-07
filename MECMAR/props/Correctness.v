From Coq Require Import PeanoNat ZArith Bool Lia Program.Equality.
From Warblre Require Import List Tactics Specialize Focus Result Base Patterns StaticSemantics Notation Semantics Definitions.

Import Result.Notations.
Import Semantics.

Module Correctness.
  Import Patterns.
  Import Notation.
  Import Semantics.

  Create HintDb Warblre.
  #[export] Hint Unfold repeatMatcherFuel wrap_option : Warblre.

  Lemma is_not_failure_true_rewrite: forall (r: option MatchState), r is not failure = true <-> r <> failure.
  Proof. intros [ | ]; split; easy. Qed.
  Lemma is_not_failure_false_rewrite: forall (r: option MatchState), r is not failure = false <-> r = failure.
  Proof. intros [ ]; split; easy. Qed.
  #[export]
  Hint Rewrite -> is_not_failure_true_rewrite is_not_failure_false_rewrite : Warblre.

  Ltac clean := repeat
  (   autounfold with Warblre_coercions in *
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
    Definition Valid (rer: RegExp) (ls: list nat) := List.Forall.Forall ls (fun i => i < RegExp.capturingGroupsCount rer).
    
(*     Lemma combine: forall rer ls ls', Valid rer ls -> Valid rer ls' -> Valid rer (ls ++ ls'). *)
  End Captures.

  Module Groups.
    Inductive Bounded: Regex -> nat -> Prop :=
    | gbEmpty: forall n, Bounded Empty n
    | gbChar: forall c n, Bounded (Char c) n
    | gbDisjunction: forall r1 r2 n, Bounded r1 n -> Bounded r2 n -> Bounded (Disjunction r1 r2) n
    | gbQuantified: forall r q n, Bounded r n -> Bounded (Quantified r q) n
    | gbSeq: forall r1 r2 n, Bounded r1 n -> Bounded r2 n -> Bounded (Seq r1 r2) n
    | gbGroup: forall r id n, (id < n)%nat -> Bounded r n -> Bounded (Group id r) n
    (* Assertions: ^ $ \b \B *)
    | gbLookahead: forall r n, Bounded r n -> Bounded (Lookahead r) n
    | gbNegativeLookahead: forall r n, Bounded r n -> Bounded (NegativeLookahead r) n
    | gbLookbehind: forall r n, Bounded r n -> Bounded (Lookbehind r) n
    | gbNegativeLookbehind: forall r n, Bounded r n -> Bounded (NegativeLookbehind r) n
    | gbBackReference: forall id n, (id < n)%nat -> Bounded (BackReference id) n.

    Lemma monotony: forall r n n',
      (n <= n')%nat -> Bounded r n -> Bounded r n'.
    Proof.
      intros.
      induction r;
        match goal with | [ H: Bounded ?r _ |- _ ] => is_compound r; dependent destruction H end;
        constructor; fforward; solve [ assumption | lia ].
    Qed.

    Local Ltac maxify n m eq :=
      let x := fresh "n" in let Tmp1 := fresh "TMP" in let Tmp2 := fresh "TMP" in
      remember (Nat.max n m) as x eqn:eq;
      assert (n <= x) as Tmp1 by lia;
      assert (m <= x) as Tmp2 by lia;
      repeat lazymatch goal with
        | [ H: Bounded ?r n |-_] => pose proof (monotony _ _ _ Tmp1 H); clear H
        | [ H: Bounded ?r m |-_] => pose proof (monotony _ _ _ Tmp2 H); clear H
      end;
      clear Tmp1 Tmp2.

    Lemma existence: forall r, exists n, Bounded r n.
    Proof.
      induction r; repeat (maxify + lazymatch goal with
        | [ H: exists n, Bounded _ n |-_] => destruct H as [ ?n H ]
        | [ n: nat, m: nat |-_] => let Tmp := fresh "TMP" in maxify n m Tmp; clear n m Tmp
        | [ n: nat |- exists _, _ ] => solve [ exists n; constructor; assumption ]
        | [ |- exists _, _ ] => solve [ exists 0; constructor; assumption ]
        end).
      - maxify n id Eq_n0. exists (n0 + 1). constructor; try lia. apply monotony with (2 := H). lia.
      - exists (id + 1). constructor. lia.
    Qed.

    Lemma capturesWithinValid: forall r rer,
      Bounded r (RegExp.capturingGroupsCount rer) -> Captures.Valid rer (capturingGroupsWithin r).
    Proof.
    Admitted.
  End Groups.

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
    ||  autounfold with Warblre_coercions in *
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
    (* Lemma characterClass_successful_state_Valid: forall input endIndex captures dir,
      ~ (step{dir} endIndex < 0)%Z  ->
      ~ (Z.of_nat (length input) < step{dir} endIndex)%Z ->
      Valid input (Definitions.characterClass_successful_state input endIndex captures dir).
    Proof. destruct dir; constructor; cbn in *; lia. Qed. *)

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
    Ltac search := autounfold with Warblre_coercions in *; subst; lazymatch goal with
    | [ H: Success _ = Success _ |- _ ] => injection H; clear H; intros H; search
    | [ H: ?c ?y = Success ?z |- exists x, MatchState.Valid _ _ _ /\ progress ?dir _ _ /\ ?c x = Success ?z ] =>
      exists y; split_conjs;
      [ assumption + ( unfold MatchState.Valid; split_conjs; try MatchState.solve )
      | try solve [Progress.saturate]
      | apply H ]
    end.

    (** TODO: move to Tactics.v *)
    Ltac fforward_impl H0 By := lazymatch type of H0 with
    | (?x = ?x) -> ?Q => specialize (H0 (eq_refl x))
    | ?P -> ?Q => lazymatch goal with
      | [ H1: P |- _ ] => specialize (H0 H1); fforward_impl H0 By
      | [ |- _ ] => let Tmp := fresh "Tmp" in assert (P) as Tmp; [ try solve[By] | specialize (H0 Tmp); clear Tmp; fforward_impl H0 By ]
      end
    | _ => idtac
    end.

    Tactic Notation "fforward" hyp(H) := fforward_impl H idtac.
    Tactic Notation "fforward" hyp(H) "as" simple_intropattern(I) := fforward_impl H idtac; destruct H as I.
    Tactic Notation "fforward" hyp(H) "by" tactic(t) := fforward_impl H t.
    Tactic Notation "fforward" hyp(H) "as" simple_intropattern(I) "by" tactic(t) := fforward_impl H t; destruct H as I.
    (** End TODO *)

    Lemma repeatMatcher: forall str rer fuel dir m min max greedy groupsWithin,
          HonoresContinuation str rer m dir ->
          HonoresContinuation str rer (fun x c => repeatMatcher' m min max greedy x c groupsWithin fuel) dir.
    Proof.
      (* The 'recursive' case (i.e. when min is not zero or the endIndex is different from last iteration) *)
      assert (forall x z s c str rer fuel dir m min max greedy groups,
        MatchState.Valid str rer x ->
        List.Update.Nat.Batch.update None (MatchState.captures x) groups = Success s ->
        HonoresContinuation str rer m dir ->
        (forall dir m min max greedy groups,
          HonoresContinuation str rer m dir ->
          HonoresContinuation str rer (Definitions.RepeatMatcher.matcher m min max greedy groups fuel) dir) ->
        (m (match_state (MatchState.input x) (MatchState.endIndex x) s)
          (Definitions.RepeatMatcher.continuation x c m min max greedy groups fuel) = Success (Some z)) ->
        exists y : MatchState,
          MatchState.Valid str rer y /\ progress dir x (Success (Some y)) /\ c y = Success (Some z)
      ) as Rec. {
        intros x z s c str rer fuel dir m min max greedy groups Vx Ex_s HCm IH Eq_rec.
        unfold HonoresContinuation in HCm, IH.
        specialize IH with (1 := HCm).
        focus § _ (_ _ []) _ § remember as d in Eq_rec.
        specialize HCm with (2 := Eq_rec).
        fforward HCm as [ y0 [ Vy0 [ Pxy0 Eq_dy0 ]] ] by MatchState.solve.
        rewrite -> Heqd in Eq_dy0. unfold Definitions.RepeatMatcher.continuation in Eq_dy0.
        focus § _ [] _ § auto destruct in Eq_dy0.
        specialize IH with (2 := Eq_dy0). fforward IH as [ y1 [ Vy1 [ Py0y1 Eq_cy1 ]]].
        search.
      }

      induction fuel; [ discriminate | ].
      cbn. intros dir m min max greedy groupsWithin HCm x c z Vx H.
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

    Lemma compileSubPattern: forall r str rer dir,
      HonoresContinuation str rer (compileSubPattern r rer dir) dir.
    Proof.
      induction r; intros str rer dir x c z; cbn;
      focus § _ [] _ -> _ § auto destruct.
      - intros; search.
      - apply characterSetMatcher.
      - intros Vx Eq_z.
        autounfold with Warblre in *.
        focus § _ [] _ § auto destruct in Eq_z.
        + injection Eq_z as ->. apply IHr1 with (2 := AutoDest_). apply Vx.
        + apply IHr2 with (2 := Eq_z). apply Vx.
      - apply repeatMatcher. apply IHr.
      - intros Vx Eq_z.
        autounfold with Warblre in *.
        focus § _ [] _ § auto destruct in Eq_z.
        + specialize IHr1 with (1 := Vx) (2 := Eq_z) as [y0 [Vy0 [Pxy0 Eq_y0]]].
          specialize IHr2 with (1 := Vy0) (2 := Eq_y0) as [y1 [Vy1 [Pxy1 Eq_y1]]].
          search.
        + specialize IHr2 with (1 := Vx) (2 := Eq_z) as [y0 [Vy0 [Pxy0 Eq_y0]]].
          specialize IHr1 with (1 := Vy0) (2 := Eq_y0) as [y1 [Vy1 [Pxy1 Eq_y1]]].
          search.
      - intros Vx Eq_z.
        autounfold with Warblre in *.
        specialize IHr with (str := str) (1 := Vx) (2 := Eq_z) as [y [Vy [Pxy Eq_y]]].
        focus § _ [] _ § auto destruct in Eq_y.
        search.
        MatchState.normalize.
        refine (List.Update.Nat.One.prop_preservation _ _ _ _ _ VCF_captures_y _ AutoDest_0).
        focus § _ [] _ § auto destruct in AutoDest_; injection AutoDest_ as <-; Zhelper; MatchState.normalize; lia.
      - intros Vx Eq_z.
        autounfold with Warblre in *.
        focus § _ [] _ § auto destruct in Eq_z.
        specialize IHr with (1 := Vx) (2 := AutoDest_) as [y [Vy [Pxy Eq_y]]].
        search.
      - intros Vx Eq_z.
        autounfold with Warblre in *.
        focus § _ [] _ § auto destruct in Eq_z.
        search.
      - intros Vx Eq_z.
        autounfold with Warblre in *.
        focus § _ [] _ § auto destruct in Eq_z.
        specialize IHr with (1 := Vx) (2 := AutoDest_) as [y [Vy [Pxy Eq_y]]].
        search.
      - intros Vx Eq_z.
        autounfold with Warblre in *.
        focus § _ [] _ § auto destruct in Eq_z.
        search.
      - apply backreferenceMatcher.
    Qed.
  End IntermediateValue.

  Module Monotony.
    Lemma compilePattern: forall r rer input i,
      progress forward (match_state input (Z.of_nat i) (List.repeat None (RegExp.capturingGroupsCount rer))) (compilePattern r rer input i).
    Proof.
      intros r rer input i.
      delta compilePattern.
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
        pose proof (IntermediateValue.compileSubPattern _ _ _ _ _ _ _ V_x Eq_z) as [y [V_y [ P_xy <- ]]].
        constructor.
        + MatchState.solve.
        + dependent destruction P_xy. assumption.
    Qed.
  End Monotony.

  Module Safety.
(*     Definition SafeContinuation (x0: MatchState) (str: list Character) (c: MatcherContinuation) (dir: direction) :=
      forall x,
        (* For any valid state *)
        MatchState.Valid str x ->
        (* which is a progress from the threshold state *)
        progress dir x0 (Success (Some x)) ->
        (* Then the overall computation does not trigger an assertion *)
        c x <> assertion_failed. *)
    Definition SafeMatcher (str: list Character) (rer: RegExp) (m: Matcher) (dir: direction) := forall x c,
      (* For any valid state *)
      MatchState.Valid str rer x ->
      (* If the overall computation runs out of fuel *)
      m x c = assertion_failed ->
      (* There is an intermediate value y that was produced by m and then passed to c which then ran out of fuel. *)
      exists y, MatchState.Valid str rer y /\ progress dir x (Success (Some y)) /\ c y = assertion_failed.
    #[export]
    Hint Unfold (*SafeContinuation*) SafeMatcher: Warblre.

(*     Lemma continuation_weakening: forall x x' str dir (c: MatcherContinuation), progress dir x (Success (Some x'))
      -> SafeContinuation x str c dir -> SafeContinuation x' str c dir.
    Proof. intros. intros y V_y P_x'_y. apply H0; try assumption. Progress.saturate. Qed. *)

    Ltac search := lazymatch goal with
    | [ H: Failure _ = assertion_failed |- _ ] => try rewrite -> H in *; clear H; search
    | [ H: ?c ?y = assertion_failed |- exists x, MatchState.Valid _ _ x /\ progress ?dir _ _ /\ ?c x = assertion_failed ] =>
      exists y; split_conjs;
      [ try Progress.solve
      | try solve [Progress.saturate]
      | apply H ]
    end.

    Lemma repeatMatcher: forall dir m min max greedy captures rer str,
      Captures.Valid rer captures ->
      SafeMatcher str rer m dir ->
      SafeMatcher str rer (fun x c => repeatMatcher m min max greedy x c captures) dir.
    Proof.
      assert (Ind: forall fuel dir m min max greedy captures rer str,
        Captures.Valid rer captures ->
        SafeMatcher str rer m dir ->
        SafeMatcher str rer (fun x c => repeatMatcher' m min max greedy x c captures fuel) dir). {
          induction fuel; intros dir m min max greedy captures rer str V_captures S_m x c V_x Eq_af; cbn in Eq_af; try easy.
          focus § _ [] _ § auto destruct in Eq_af.
          - search.
          - apply S_m in Eq_af as [ y0 [ V_y0 [ P_x_y0 Eq_af ]]]; try MatchState.solve.
            + focus § _ [] _ § auto destruct in Eq_af.
              apply (IHfuel _ _ _ _ greedy captures _ str V_captures S_m _ c V_y0) in Eq_af as [ y1 [ V_y1 [ P_y0_y1 Eq_af ]]].
              search.
          - apply S_m in Eq_af as [ y0 [ V_y0 [ P_x_y0 Eq_af ]]]; try MatchState.solve.
            focus § _ [] _ § auto destruct in Eq_af.
            apply (IHfuel _ _ _ _ greedy captures _ str V_captures S_m _ c V_y0) in Eq_af as [ y1 [ V_y1 [ P_y0_y1 Eq_af ]]].
            search.
          - rewrite <- Eq_af. search.
          - search.
          - injection Eq_af as ->.
            apply S_m in AutoDest_3 as [ y0 [ V_y0 [ P_x_y0 Eq_af ]]]; try MatchState.solve.
            focus § _ [] _ § auto destruct in Eq_af.
            apply (IHfuel _ _ _ _ greedy captures _ str V_captures S_m _ c V_y0) in Eq_af as [ y1 [ V_y1 [ P_y0_y1 Eq_af ]]].
            search.
          - injection Eq_af as ->.
            apply List.Update.Nat.Batch.failure_bounds in AutoDest_0. unfold Captures.Valid in V_captures.
            destruct V_x as [ _ [ _ [ VCL_x _ ]]]. rewrite -> VCL_x in *. contradiction.
      }
      intros dir m min max greedy captures rer str H H0 x c H1 H2. specialize Ind with (1 := H) (2 := H0).
      unfold repeatMatcher. unfold SafeMatcher in Ind.
      apply Ind with (1 := H1) (2 := H2).
      Qed.

    Lemma characterSetMatcher: forall str rer A invert dir,
      SafeMatcher str rer (characterSetMatcher rer A invert dir) dir.
    Proof.
      intros str rer A invert dir x c Vx Eq_oof.
      unfold characterSetMatcher in Eq_oof. focus § _ [] _ § auto destruct in Eq_oof.
      - search.
        + Zhelper. MatchState.solve_with lia.
        + apply Progress.step. lia.
      - injection Eq_oof as ->. apply List.Exists.failure_kind in AutoDest_1.
        destruct AutoDest_1 as [ i [ v [ Indexed_A_i Eq_v_s ]]].
        discriminate.
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
      n < RegExp.capturingGroupsCount rer ->
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
        pose proof Eq_indexed as Tmp. apply List.Range.indexing in Tmp as ->.
        apply List.Indexing.Int.success_bounds in Eq_indexed as Bounds_i. clear Eq_indexed.
        destruct Vx as [ Eq_str [ [ ? ? ] [ _ V_t ]]]. specialize (V_t _ _ AutoDest_). dependent destruction V_t.
        rename s into t_s, e into t_e, H into Ineq_t, H0 into IO_t_s, H1 into IO_t_e.
        MatchState.normalize. cbn in *. rewrite -> List.Range.length in *.
        focus § _ [] _ § auto destruct in Eq_af; injection Eq_af as ->.
        + destruct dir.
          * apply List.Indexing.Int.failure_bounds in AutoDest_1 as [ ? | ? ]; lia.
          * apply List.Indexing.Int.failure_bounds in AutoDest_1 as [ ? | ? ]; lia.
        + destruct dir.
          * apply List.Indexing.Int.failure_bounds in AutoDest_0 as [ ? | ? ]; lia.
          * apply List.Indexing.Int.failure_bounds in AutoDest_0 as [ ? | ? ]; lia.
      - injection Eq_af as ->.
        apply List.Indexing.Nat.failure_bounds in AutoDest_.
        destruct Vx as [ _ [ _ [ Tmp _ ]]]; rewrite -> Tmp in *; clear Tmp.
        lia.
    Qed.

    Lemma compileSubPattern: forall r dir str rer,
      Groups.Bounded r (RegExp.capturingGroupsCount rer) ->
      SafeMatcher str rer (compileSubPattern r rer dir) dir.
    Proof.
      induction r; cbn; intros dir str rer GB_r; dependent destruction GB_r.
      - intros x c Vx Sc. search.
      - apply characterSetMatcher.
      - intros x c Vx Sc.
        focus § _ [] _ § auto destruct in Sc.
        + unfold SafeMatcher in IHr2.
          specialize IHr2 with (1 := GB_r2) (dir := dir) (str := str) (x := x) (c := c). fforward.
          destruct IHr2 as [ ? [ ? [ ? ? ]]]. search.
        + injection Sc as ->.
          unfold SafeMatcher in IHr1.
          specialize IHr1 with (1 := GB_r1) (dir := dir) (str := str) (x := x) (c := c). fforward.
          destruct IHr1 as [ ? [ ? [ ? ? ]]]. search.
      - apply repeatMatcher.
        + apply Groups.capturesWithinValid. assumption.
        + apply IHr. assumption.
      - intros x c V_x S_c. destruct dir.
        + specialize (IHr1 _ _ _ GB_r1 _ _ V_x S_c) as [ y0 [ V_y0 [ P_x_y0 Eq_y0 ]]].
          specialize (IHr2 _ _ _ GB_r2 _ _ V_y0 Eq_y0) as [ y1 [ V_y1 [ P_x_y1 Eq_y1 ]]].
          search.
        + specialize (IHr2 _ _ _ GB_r2 _ _ V_x S_c) as [ y0 [ V_y0 [ P_x_y0 Eq_y0 ]]].
          specialize (IHr1 _ _ _ GB_r1 _ _ V_y0 Eq_y0) as [ y1 [ V_y1 [ P_x_y1 Eq_y1 ]]].
          search.
      - intros x c V_x Eq_af.
        specialize (IHr _ _ _ GB_r _ _ V_x Eq_af) as [ y0 [ V_y0 [ P_x_y0 Eq_y0 ]]].
        focus § _ [] _ § auto destruct in Eq_y0.
        + focus § _ [] _ § auto destruct in AutoDest_.
          * search. MatchState.solve_with lia.
          * search. MatchState.solve_with lia.
        + injection Eq_y0 as ->. apply List.Update.Nat.One.failure_bounds in AutoDest_0.
          MatchState.solve_with lia.
        + injection Eq_y0 as ->.
          focus § _ [] _ § auto destruct in AutoDest_; destruct dir; try discriminate.
          * Zhelper. MatchState.normalize.
            dependent destruction P_x_y0.
            dependent destruction H1. cbn in *.
            lia.
          * Zhelper.
            dependent destruction P_x_y0.
            dependent destruction H1. cbn in *.
            lia.
      - apply positiveLookaroundMatcher with (dir' := forward).
        + apply IntermediateValue.compileSubPattern.
        + apply IHr. assumption.
      - apply negativeLookaroundMatcher with (dir' := forward). apply IHr. assumption.
      - apply positiveLookaroundMatcher with (dir' := backward).
        + apply IntermediateValue.compileSubPattern.
        + apply IHr. assumption.
      - apply negativeLookaroundMatcher with (dir' := backward). apply IHr. assumption.
      - apply backreferenceMatcher. assumption.
    Qed.

    Theorem compilePattern: forall r rer input i,
      Groups.Bounded r (RegExp.capturingGroupsCount rer) ->
      0 <= i <= (length input) ->
      compilePattern r rer input i <> assertion_failed.
    Proof.
      intros r rer input i GB Bounds_i. delta compilePattern. cbn.
      focus § _ (_ [] _) § auto destruct.
      - hypotheses_reflector. spec_reflector Nat.leb_spec0. contradiction.
      - remember (match_state input i (List.repeat None (RegExp.capturingGroupsCount rer))) as x eqn:Eq_x.
        pose proof (Safety.compileSubPattern _ forward input _ GB x (fun y => y)) as Falsum.
        assert (MatchState.Valid input rer x) as V_x. {
          subst x. apply MatchState.valid_init. lia.
        }
        focus § _ (_ [] _) § do (fun t => destruct t as [ | f ]; try easy; destruct f; try easy).
        fforward. destruct Falsum as [ ? [ _ [ _ ? ]]].
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
    #[export]
    Hint Unfold TerminatingMatcher: Warblre.

    Definition remainingChars (x: MatchState) (dir: direction): nat := match dir with
    | forward => length (MatchState.input x) - Z.to_nat (MatchState.endIndex x)
    | backward => Z.to_nat (MatchState.endIndex x)
    end.
    Definition fuelBound (min: non_neg_integer) (x: MatchState) (dir: direction) := min + (remainingChars x dir)  + 1.
    #[export]
    Hint Unfold fuelBound remainingChars : Warblre.

    Lemma repeatMatcherFuel_satisfies_bound: forall min x str rer dir, MatchState.Valid str rer x -> fuelBound min x dir <= repeatMatcherFuel min x.
    Proof. intros. autounfold with Warblre in *. destruct H as [ <- [ [ Bounds_Ei_x_low Bounds_Ei_x_high ] VC_x ] ]. destruct dir; cbn; lia. Qed.

    Lemma fuelDecreases_min: forall dir min min' x x' b,
      min' < min -> progress dir x (Success (Some x')) -> fuelBound min x dir <= S b -> fuelBound min' x' dir <= b.
    Proof.
      intros. autounfold with Warblre in *. inversion H0; destruct dir; inversion H6; subst.
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

    Lemma repeatMatcher': forall fuel m min max greedy captures x c dir str rer,
      fuelBound min x dir <= fuel ->
      MatchState.Valid str rer x ->
      TerminatingMatcher str rer m dir ->
      repeatMatcher' m min max greedy x c captures fuel = out_of_fuel ->
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
    
      induction fuel; intros m min max greedy captures x c dir str rer Ineq_fuel Vx Tm Falsum.
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

    Lemma repeatMatcher: forall m min max greedy captures str rer dir,
      TerminatingMatcher str rer m dir ->
      TerminatingMatcher str rer (fun x c => repeatMatcher m min max greedy x c captures) dir.
    Proof.
      unfold Semantics.repeatMatcher, TerminatingMatcher. intros m min max greedy captures str rer dir Tm x c V_x Eq_oof.
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
      - injection Eq_oof as ->. apply List.Exists.failure_kind in AutoDest_1.
        destruct AutoDest_1 as [ i [ v [ Indexed_A_i Eq_v_s ]]].
        discriminate.
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
        focus § _ [] _ § auto destruct in Eq_oof.
        + injection Eq_oof as ->.
          pose proof (@List.Indexing.Int.failure_kind Character) as Falsum. specialize Falsum  with (1 := AutoDest_4).
          cbn in *. congruence.
        + injection Eq_oof as ->.
          pose proof (@List.Indexing.Int.failure_kind Character) as Falsum. specialize Falsum  with (1 := AutoDest_3).
          cbn in *. congruence.
      - injection Eq_oof as ->.
        pose proof @List.Indexing.Nat.failure_kind as Falsum. specialize Falsum  with (1 := AutoDest_).
        cbn in *. congruence.
    Qed.

    Lemma compileSubPattern: forall r rer dir str, TerminatingMatcher str rer (compileSubPattern r rer dir) dir.
    Proof.
      induction r; intros rer dir str; cbn -[Semantics.repeatMatcher];
      focus § _ [] _ § auto destruct.
      - intros x c Vx H. search.
      - apply characterSetMatcher.
      - intros x c Vx H. autounfold with Warblre in *. focus § _ [] _ § auto destruct in H; repeat (specialize_once; bookkeeper); search.
      - apply repeatMatcher. apply IHr.
      - intros x c Vx H. autounfold with Warblre in *.
        specialize IHr1 with (1 := Vx) (2 := H) as [ y0 [ Vy0 [ P_x_y0 Eq_oof0 ]]].
        specialize IHr2 with (1 := Vy0) (2 := Eq_oof0) as [ y1 [ Vy1 [ P_y0_y1 Eq_oof1 ]]].
        search.
      - intros x c Vx H. autounfold with Warblre in *.
        specialize IHr2 with (1 := Vx) (2 := H) as [ y0 [ Vy0 [ P_x_y0 Eq_oof0 ]]].
        specialize IHr1 with (1 := Vy0) (2 := Eq_oof0) as [ y1 [ Vy1 [ P_y0_y1 Eq_oof1 ]]].
        search.
      - intros x c Vx H. autounfold with Warblre in *. 
        specialize IHr with (str := str) (1 := Vx) (2 := H).
        destruct IHr as [ y [ Vy [ P_x_y Eq_oof ]]].
        focus § _ [] _ § auto destruct in Eq_oof.
        + search. MatchState.normalize; try MatchState.solve.
          apply List.Update.Nat.One.prop_preservation with (ls := captures_y) (i := id) (v := s); try assumption.
          focus § _ [] _ § auto destruct in AutoDest_; injection AutoDest_ as <-; constructor; solve [ assumption | lia ].
        + rewrite -> List.Update.Nat.One.failure_kind with (f := f) in AutoDest_0 by assumption.
          injection AutoDest_0 as <-. discriminate.
        + focus § _ [] _ § auto destruct in AutoDest_.
          * injection AutoDest_ as <-. discriminate.
          * injection AutoDest_ as <-. discriminate.
      - apply positiveLookaroundMatcher with (dir' := forward).
        + apply IntermediateValue.compileSubPattern.
        + apply IHr.
      - apply negativeLookaroundMatcher with (dir' := forward). apply IHr.
      - apply positiveLookaroundMatcher with (dir' := backward).
        + apply IntermediateValue.compileSubPattern.
        + apply IHr.
      - apply negativeLookaroundMatcher with (dir' := backward). apply IHr.
      - apply backreferenceMatcher.
    Qed.

    Lemma compilePattern: forall r rer input i, compilePattern r rer input i <> out_of_fuel.
    Proof.
      intros. delta compilePattern. cbn.
      focus § _ (_ [] _) § auto destruct.
      (focus § _ (_ [] _) § do (fun t => destruct t eqn:S)); try easy.
      destruct f; try easy.
      pose proof compileSubPattern as Falsum. autounfold with Warblre in *. specialize Falsum with (str := input) (2 := S).
      focus § [] -> _ § do (fun t => assert(t)) in Falsum.
      - apply MatchState.valid_init. boolean_simplifier. spec_reflector Nat.leb_spec0. lia.
      - specialize Falsum with (1 := H). Coq.Program.Tactics.destruct_conjs. discriminate.
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