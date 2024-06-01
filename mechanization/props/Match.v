From Coq Require Import PeanoNat ZArith Bool Lia Program.Equality List.
From Warblre Require Import List Tactics Retrieve Specialize Focus Result Base Patterns Node NodeProps StaticSemantics Notation Semantics Definitions EarlyErrors Compile RegExpRecord.

Import Result.Notations.
Import Semantics.
Import Coercions.

Module Correctness.
  Import Patterns.
  Import Notation.
  Import Semantics.

  (** Progress: We say that a MatchState (wrapped in Result) ry has progressed w.r.t to another MatchState x if:
      - ry = Success y, x and y share the same input string and either
        + direction is forward, in which case x's endIndex <= y's endIndex
        + direction is backward, in which case y's endIndex <= x's endIndex
      - ry is any kind of failure
  *)

  Module Captures.
    Definition Valid (rer: RegExpRecord) (parenIndex parenCount: non_neg_integer) :=
      List.Forall.Forall (List.Range.Nat.Bounds.range (parenIndex) (parenIndex + parenCount)) (fun i => i < RegExpRecord.capturingGroupsCount rer).
  End Captures.

  (* Allows to abstract most theorem over the direction of progress *)
  Inductive directionalProgress `{Parameters}: Direction -> MatchState -> MatchState -> Prop :=
  | dpForward: forall x y, (MatchState.endIndex x <= MatchState.endIndex y)%Z -> directionalProgress forward x y
  | dpBackward: forall x y, (MatchState.endIndex x >= MatchState.endIndex y)%Z -> directionalProgress backward x y.

  Inductive progress `{Parameters}: Direction -> MatchState -> MatchResult -> Prop :=
  | pStep: forall dir x y, 
      (MatchState.input x) = (MatchState.input y)
    -> directionalProgress dir x y
    -> progress dir x (Success (Some y))
  | pMismatch: forall dir x, progress dir x failure
  | pError: forall dir x f, progress dir x (Error f).
  #[export]
  Hint Constructors progress: core.

  Definition IteratorOn `{Parameters} (str: list Character) (i: Z) := (0 <= i <= Z.of_nat (length str))%Z.

  Module CaptureRange. Section main.
    Context `{specParameters: Parameters}.

    Inductive Valid (str: list Character): option CaptureRange -> Prop :=
    | vCrDefined: forall s e, ( s <= e -> IteratorOn str s -> IteratorOn str e -> Valid str (Some (capture_range s e)) )%Z
    | vCrUndefined: Valid str undefined.
    End main.

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
        | [ VCs : List.Forall.Forall ?c (Valid ?str),
            Indexed : (?c [?n]) = Success (Some (capture_range ?s ?e))
          |- _ ] => is_var c; lazymatch goal with
                    | [ _: (s <= e)%Z |- _ ] => fail
                    | [ |- _ ] => let H := fresh "VCR_" s "_" e in
                                  cbn in Indexed; focus <! _ [] _ !> auto destruct in Indexed;
                                  pose proof (VCs _ _ Indexed) as H;
                                  dependent destruction H
                    end
        | [ VC: Valid _ (Some (capture_range ?s ?e)) |- _ ] =>
            dependent destruction VC
        | [ |- Valid _ _ ] => constructor
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
        H: List.Forall.Forall ?c (Valid ?str)
        |- List.Forall.Forall ?c' _ ] =>
          refine (List.Update.Nat.One.prop_preservation _ _ _ _ _ H _ Eq); constructor; unfold IteratorOn; t
    | [ H: List.Forall.Forall ?oc (Valid ?str),
        Eq: List.Update.Nat.Batch.update _ ?oc _ = Success ?nc
      |- List.Forall.Forall ?nc (Valid ?str) ] =>
          refine (List.Update.Nat.Batch.prop_preservation _ _ _ _ _ H _ Eq); solve [ constructor | assumption | t ]
    end.

    Local Ltac solve_impl t := solve [ normalize; (solvers || t) ].

    Ltac solve := solve_impl idtac.
    Ltac solve_with t := solve_impl t.
  End CaptureRange.

  Module MatchState. Section main.
    Context `{specParameters: Parameters}.

    Definition OnInput (str: list Character) (x: MatchState) := MatchState.input x = str.
    Definition Valid (str: list Character) (rer: RegExpRecord) (x: MatchState) :=
      OnInput str x /\
      IteratorOn str (MatchState.endIndex x) /\
      length (MatchState.captures x) = RegExpRecord.capturingGroupsCount rer /\
      List.Forall.Forall (MatchState.captures x) (CaptureRange.Valid str).

    Definition remainingChars (x: MatchState) (dir: Direction): nat := match dir with
    | forward => length (MatchState.input x) - Z.to_nat (MatchState.endIndex x)
    | backward => Z.to_nat (MatchState.endIndex x)
    end.

    Lemma change_captures: forall str rer input endIndex cap cap',
      length cap' = RegExpRecord.capturingGroupsCount rer ->
      List.Forall.Forall cap' (CaptureRange.Valid str) ->
      Valid str rer (match_state input endIndex cap) ->
      Valid str rer (match_state input endIndex cap').
    Proof.
      intros str rer input endIndex cap cap' H0 H1 [ OI_x [ IO_x V_cap ]].
      unfold Valid. split_conjs; try assumption.
    Qed.

    Lemma self_input: forall str rer x, Valid str rer x -> Valid (MatchState.input x) rer x.
    Proof. intros ? ? ? (<-&?&?&?). unfold Valid; split_conjs; try assumption. reflexivity. Qed.

    Lemma step: forall str rer x dir n, Valid str rer x ->
      (0 <= n)%Z ->
      (n <= remainingChars x dir)%Z ->
      Valid (MatchState.input x) rer
        (match_state str
           (if dir == forward
            then (MatchState.endIndex x + n)%Z
            else (MatchState.endIndex x - n)%Z) (MatchState.captures x)).
    Proof.
      intros ? ? [ ] ? ? (<-&?&?&?) ? ?. unfold Valid,IteratorOn in *; cbn in *.
      split_conjs; try assumption; try reflexivity.
      all: destruct dir; cbn in *; try lia.
    Qed.

    End main.

    (*  Normalizes all MatchStates by doing the following:
        - Destructing them into their components
        - Then, if the MatchState is known to be on a particular string, eliminate the string introduced at the previous step. *)
    Ltac normalize := repeat
    (   CaptureRange.normalize
    ||  unfold remainingChars
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
          try rewrite <- H in *(*; clear H; clear input*)
        | [ H: Valid ?str _ (match_state ?input ?endIndex ?captures) |- _ ] =>
          let OI := fresh "Eq_" input in
          let Iterx := fresh "Iter_" endIndex in
          let VCL := fresh "VCL_" captures in
          let VCF := fresh "VCF_" captures in
          destruct H as [ OI [ Iterx [ VCL VCF ]]]; rewrite <- OI in *; clear OI
        | [ |- Valid _ _ _ ] =>
          unfold Valid; split_conjs

        | [ H: List.Update.Nat.One.update _ _ _ = Success _ |- _ ] =>
          pose proof (List.Update.Nat.One.success_length _ _ _ _ H) as <-
        | [ H: List.Update.Nat.Batch.update _ _ _ = Success _ |- _ ] =>
          pose proof (List.Update.Nat.Batch.success_length _ _ _ _ H) as <-
        end).

    Ltac solvers t := assumption || reflexivity || CaptureRange.solvers t
      || lazymatch goal with
          | [ H1: List.Forall.Forall ?ls (CaptureRange.Valid ?input),
              H3: List.Update.Nat.One.update ?v ?ls _ = Success ?ls',
              Eq: _ = Success ?v
              |- List.Forall.Forall ?ls' (CaptureRange.Valid ?input) ] =>
              apply List.Update.Nat.One.prop_preservation with (1 := H1) (3 := H3);
              (* Goal: CaptureRange.Valid _ ?v *)
              try solve [ focus <! _ [] _ !> auto destruct in Eq; injection Eq as <-; constructor; (assumption + lia) ]
          end.
    (* Solves the current goal by 1. normalizing the states 2. leveraging assumptions and reflexivity *)
    Local Ltac solve_impl t := solve [ normalize; unfold OnInput, Valid; (solvers t || t) ].

    Ltac solve := solve_impl idtac.
    Ltac solve_with t := solve_impl t.


    Definition init `{Parameters} (rer: RegExpRecord) (str: list Character) (i: nat) := (match_state str (Z.of_nat i) (List.repeat None (RegExpRecord.capturingGroupsCount rer))).

    Lemma valid_init `{Parameters}: forall rer str i, (i <= length str) -> Valid str rer (init rer str i).
    Proof.
      intros rer str i Ineq_i. normalize; try MatchState.solve_with lia.
      - apply List.repeat_length.
      - apply List.Forall.repeat. constructor.
    Qed.
  End MatchState.

  Module Progress. Section main.
    Context `{specParameters: Parameters}.

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
        (if dir == forward
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
    End main.

    (*  Normalize the hypotheses/goals related to progress:
        - Normalize all MatchStates (using MatchState.normalize)
        - Uniformizes all captures, which are irrelevant to progress (replaces all of them by DMap.empty)
        - Derives that two MatchStates have the same input from progress hypotheses *)
    Ltac normalize := repeat (
        MatchState.normalize
    ||  rewrite <- (ignores_captures_l (List.empty)) in *
    ||  rewrite <- (ignores_captures_r (List.empty)) in *
    ||  lazymatch goal with
        | [ H: progress forward _ _ |- _ ] => dependent destruction H
        | [ H: directionalProgress forward _ _ |- _ ] => dependent destruction H
        | [ H: progress backward _ _ |- _ ] => dependent destruction H
        | [ H: directionalProgress backward _ _ |- _ ] => dependent destruction H
        | [ |- progress forward _ _ ] => constructor; constructor
        | [ |- progress backward _ _ ] => constructor; constructor
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

    Local Ltac saturate_step dir x e := match goal with
    | [ H: progress dir x (Success (Some e)) |- _ ] => apply H
    | [ H1: progress dir x (Success (Some ?y)), H2: progress dir ?y (Success ?z) |- _ ] =>
      lazymatch goal with
      | [ _: progress dir x (Success (Some z)) |- _ ] => fail
      | [ |- _ ] =>
          let H := fresh "ps_trans_" H1 H2 in
          pose proof (Progress.trans _ _ _ _ H1 H2) as H
      end
    end.

    (* Saturates the progress hypotheses by transitivity. Then attemps to solve goals using assumptions and reflexivity. *)
    Ltac saturate := normalize; match goal with
    | [ |- progress ?dir ?x (Success (Some ?x)) ] => apply refl
    | [ |- progress ?dir ?x (Success (Some ?y)) ] => repeat (saturate_step dir x y; normalize) (*; normalize; try solvers *)
    end.
  End Progress.


  Module MatcherInvariant. Section main.
    Context `{specParameters: Parameters}.

    Section Definitions.
      (* A matcher m satisfies the invariant if *)
      Definition matcher_invariant (m: Matcher) (dir: Direction) (rer: RegExpRecord) :=
          (* For all state x and continuation c *)
          forall x c,
          (* Such that x is valid *)
          MatchState.Valid (MatchState.input x) rer x ->
          (* Then either *)
            (* The match fails *)
            (m x c = failure) \/
            (* or *)
            (* m did some work, yielding a new state y, which *)
            (exists y,
              (* Is valid *)
              MatchState.Valid (MatchState.input x) rer y /\
              (* Is a progress w.r.t x *)
              progress dir x (Success (Some y)) /\
              (* Was passed to the continuation to conclude *)
              c y = m x c).

      (* Variant of the matcher_invariant, whose invariant only holds for specific states x satisfying P *)
      Definition conditional_matcher_invariant (P: MatchState -> Prop) (m: Matcher) (dir: Direction) (rer: RegExpRecord) :=
          forall x c,
          P x ->
          MatchState.Valid (MatchState.input x) rer x ->
            (m x c = failure) \/
            (exists y, MatchState.Valid (MatchState.input x) rer y /\ progress dir x (Success (Some y)) /\ c y = m x c).
    End Definitions.

    (** Some (internal) tactics to reason with the matcher_invariant. You should most likely use the 'API' defined later. *)
    Ltac base_reasoning := autounfold with result_wrappers in *; Result.inject_all; subst; repeat lazymatch goal with
    | [ |- ?x = ?x \/ _ ] => left; reflexivity
    | [ |- Error _ = Success None \/ _ ] => right
    end.

    Ltac search := intros; base_reasoning; lazymatch goal with
    | [ H: ?c ?y = ?r |- _ \/ (exists x, MatchState.Valid _ _ x /\ progress ?dir _ _ /\ ?c x = ?r) ] => right; search
    | [ |- _ \/ (exists x, MatchState.Valid _ _ x /\ progress ?dir _ _ /\ ?c x = ?c ?y) ] => right; search
    | [ H: ?P |- ?P \/ _ ] => left; apply H
    | [ H: ?P |- _ \/ ?P ] => right; apply H
    | [ H: ?c ?y = ?r |- exists x, MatchState.Valid _ _ x /\ progress ?dir _ _ /\ ?c x = ?r ] =>
      exists y; split; [ | split ];
      [ try Progress.solve
      | try solve [Progress.saturate]
      | apply H ]
    | [ |- exists x, MatchState.Valid _ _ x /\ progress ?dir _ _ /\ ?c x = ?c ?y ] =>
      exists y; split; [ | split ];
      [ try Progress.solve
      | try solve [Progress.saturate]
      | reflexivity ]
    end.

    Ltac eval_matcher H := lazymatch goal with
    | [ |- matcher_invariant ?m _ _ ] =>
        let x := fresh "x" in
        let c := fresh "c" in
        let Vx := fresh "V_" x in
        intros x c Vx; destruct m eqn:H; cbn in H; focus <! _ [] _ !> auto destruct in H
    | [ |- ?res = _ \/ (exists y : MatchState, MatchState.Valid (MatchState.input ?x) _ y /\ progress _ ?x (Success (Some y)) /\ ?c y = ?res)] =>
        destruct res eqn:H; cbn in H; focus <! _ [] _ !> auto destruct in H
    | [ H: ?m ?x ?c = ?res |- ?res = _ \/ (exists y : MatchState, MatchState.Valid (MatchState.input ?x) _ y /\ progress _ ?x (Success (Some y)) /\ ?c y = ?res)] =>
        cbn in H; focus <! _ [] _ !> auto destruct in H
    end; autounfold with result_wrappers in *; repeat match goal with [ H: Success _ = Success _ |- _ ] => injection H as H end.

    Lemma mi_application_match: forall (m: Matcher) dir rer x c z
      (MI: matcher_invariant m dir rer)
      (V_x: MatchState.Valid (MatchState.input x) rer x)
      (Eq_z: m x c = Success (Some z)),
      exists y, MatchState.Valid (MatchState.input x) rer y /\ progress dir x (Success (Some y)) /\ c y = (Success (Some z)).
    Proof. intros. specialize (MI x c V_x) as [H | H]. - rewrite -> Eq_z in H. discriminate. - rewrite -> Eq_z in H. apply H. Qed.

    Lemma mi_application_success: forall (m: Matcher) dir rer x c z
      (MI: matcher_invariant m dir rer)
      (V_x: MatchState.Valid (MatchState.input x) rer x)
      (Eq_z: m x c = Success z),
      z = None \/ exists y, MatchState.Valid (MatchState.input x) rer y /\ progress dir x (Success (Some y)) /\ c y = (Success z).
    Proof. intros. specialize (MI x c V_x) as [H | H]. - rewrite -> Eq_z in H. injection H as ->. left. reflexivity. - rewrite -> Eq_z in H. right. apply H. Qed.

    Lemma mi_application_failure: forall (m: Matcher) dir rer x c f
      (MI: matcher_invariant m dir rer)
      (V_x: MatchState.Valid (MatchState.input x) rer x)
      (Eq_z: m x c = Error f),
      exists y, MatchState.Valid (MatchState.input x) rer y /\ progress dir x (Success (Some y)) /\ c y = Error f.
    Proof. intros. specialize (MI x c V_x) as [H | H]. - rewrite -> Eq_z in H. discriminate. - rewrite -> Eq_z in H. apply H. Qed.


    Lemma mi_application_generic: forall (m: Matcher) dir rer x c r
      (MI: matcher_invariant m dir rer)
      (V_x: MatchState.Valid (MatchState.input x) rer x)
      (Eq_z: m x c = r),
      r = None \/ exists y, MatchState.Valid (MatchState.input x) rer y /\ progress dir x (Success (Some y)) /\ c y = r.
    Proof. intros. specialize (MI x c V_x) as [? | ?]; subst. - left; assumption. - right; assumption. Qed.

    Ltac apply_mi_in_goal H By :=
      lazymatch type of H with
      | matcher_invariant ?m ?dir ?rer =>
        lazymatch goal with
        | [|- m ?x ?c = Success None \/ (exists y, _ /\ _ /\ _ y = m ?x ?c) ] =>
            let tmp := fresh "Tmp" in
            pose proof (H x c) as [-> | tmp]; [ By | left; reflexivity |
              let y := fresh "x" in
              let Vy := fresh "V_" y in
              let Py := fresh "P_" y in
              destruct tmp as (y & Vy & Py & <-) ]
        | [|- _ ] => fail "Goal does not look like a matcher invariant..."
        end
      | ?T => fail "Applied invariant has incorrect type:" T
      end.

    Ltac einstance H := lazymatch type of H with
    | forall (_: ?T), _ =>
        let x := fresh "eTmp" in
        evar (x : T);
        let x' := (eval unfold x in x) in
        clear x; specialize (H x'); einstance H
    | _ => idtac
    end.

    Ltac apply_mi_in_hyp H In As By :=
      let apply_theorems := fun H m dir rer =>
        lazymatch type of In with
        | ?m' ?x ?c = ?r =>
            unify m m';
            lazymatch r with
            | Success (Some ?y) => apply (mi_application_match m dir rer x c y H) in In as As; [ | .. | By ]
            | Success ?y        => apply (mi_application_success m dir rer x c y H) in In as As; [ | .. | By ]
            | Error ?f        => apply (mi_application_failure m dir rer x c f H) in In as As; [ | .. | By ]
            | ?r                => apply (mi_application_generic m dir rer x c r H) in In as As; [ | .. | By ]
            | ?T => fail "Target hypothesis has incorrect type:" T
            end
        | ?T => fail "Target hypothesis has incorrect type (or could not unify):" T
        end
      in
      let check_trimmed := fun H => 
        lazymatch type of H with
        | matcher_invariant ?m ?dir ?rer => apply_theorems H m dir rer
        | ?T => fail "Applied invariant has incorrect type:" T
        end
      in
      lazymatch type of H with
      | forall _, _ =>
          let tmp := fresh "Tmp" in
          pose proof H as tmp;
          einstance tmp;
          check_trimmed tmp;
          clear tmp
      | _ => check_trimmed H
      end.

    (** 'API' for the tactics we just defined, and some other useful lemmas *)
    Ltac quick_math := repeat (
      boolean_simplifier ||
      spec_reflector Nat.eqb_spec ||
      spec_reflector Nat.leb_spec0 ||
      spec_reflector Z.eqb_spec ||
      spec_reflector Z.ltb_spec0 ||
      spec_reflector Z.leb_spec0 ||
      normalize_Z_comp).

    Tactic Notation "run" "matcher" "as" ident(H) := eval_matcher H.
    Tactic Notation "apply_mi" constr(H) := (apply_mi_in_goal H idtac).
    Tactic Notation "apply_mi" constr(H) "by" tactic1(By) := (apply_mi_in_goal H By).
    Tactic Notation "apply_mi" constr(H) "in" hyp(In) "as" simple_intropattern(As) := (apply_mi_in_hyp H In As idtac).
    Tactic Notation "apply_mi" constr(H) "in" hyp(In) "as" simple_intropattern(As) "by" tactic1(By) := (apply_mi_in_hyp H In As By).

    Lemma directional_min_rewrite: forall i r dir,
      (0 <= r)%Z ->
      Z.min
        (i)
        (if dir == forward
           then (i + r)%Z
           else (i - r)%Z)
      = if dir == forward then i else (i - r)%Z.
    Proof.
      intros ? ? [ | ] ?; cbn;
        lazymatch goal with
          | [ |- context[ Z.min ?i (?i + ?r)%Z ] ] =>
              replace (Z.min i (i + r)) with i in * by lia
          | [ |- context[ Z.min ?i (?i - ?r)%Z ] ] =>
              replace (Z.min i (i - r)) with (i - r)%Z in * by lia
          end; reflexivity.
    Qed.

    (** We now prove that all construced matchers satisfy the (conditional) matcher invariant *)

    Lemma characterSetMatcher: forall rer A invert dir,
      matcher_invariant (characterSetMatcher rer A invert dir) dir rer.
    Proof.
      intros rer A invert dir. unfold characterSetMatcher.
      run matcher as Matching; autounfold with result_wrappers in *.
      1-3: search.
      - search. +  Zhelper. MatchState.solve_with lia. + apply Progress.step. lia.
      - search. +  Zhelper. MatchState.solve_with lia. + apply Progress.step. lia.
      - Result.inject_all; subst.
        ltac2:(retrieve (List.Indexing.Int.indexing _ _ = Error _) as H).
        apply List.Indexing.Int.failure_bounds in H.
        quick_math.
        destruct V_x as [ Eq_str [ [ ? ? ] _ ]]. rewrite -> directional_min_rewrite in * by lia.
        destruct dir; cbn in *; lia.
    Qed.

    Section RepeatMatcher.
      (* Leverage additional definitions to make the terms more readable, by collapsing big terms into definitions *)
      Ltac fold_matchers := lazymatch goal with
      | [ _: context[ repeatMatcher' ?m ?min ?max ?greedy ?x ?c ?parenIndex ?parenCount ?fuel ] |- _ ] =>
          replace (repeatMatcher' m min max greedy x c parenIndex parenCount fuel) with (Definitions.RepeatMatcher.matcher m min max greedy parenIndex parenCount fuel x c) in * by reflexivity
      | [ _: context[ fun y : MatchState =>
                if
                 ?min == 0 &&
                 (MatchState.endIndex y =? MatchState.endIndex ?x)%Z
                then Success None
                else
                 repeatMatcher' ?m (if ?min == 0 then 0 else ?min - 1)
                   (if (?max =? +∞)%NoI then +∞ else (?max - 1)%NoI)
                   ?greedy y ?c ?parenIndex ?parenCount ?fuel ] |- _ ] =>
                replace (fun y : MatchState =>
                if
                 min == 0 &&
                 (MatchState.endIndex y =? MatchState.endIndex x)%Z
                then Success None
                else
                 repeatMatcher' m (if min == 0 then 0 else min - 1)
                   (if (max =? +∞)%NoI then +∞ else (max - 1)%NoI)
                   greedy y c parenIndex parenCount fuel) with (Definitions.RepeatMatcher.continuation x c m min max greedy parenIndex parenCount fuel) in * by reflexivity
      end.

      (* A more precise bound on the amount of fuel required for the repeatMatcher to terminate *)
      (* Here, we additionally have access to the direction of the matcher, which allows for a more precise bound *)
      Definition fuelBound (min: non_neg_integer) (x: MatchState) (dir: Direction) := min + (MatchState.remainingChars x dir)  + 1.

      (* This new bound is always lower than the original bound *)
      Lemma repeatMatcherFuel_satisfies_bound: forall min x rer dir, MatchState.Valid (MatchState.input x) rer x -> fuelBound min x dir <= repeatMatcherFuel min x.
      Proof. intros. unfold fuelBound,repeatMatcherFuel in *. destruct H as [ ? [ [ Bounds_Ei_x_low Bounds_Ei_x_high ] VC_x ] ]. destruct dir; cbn; lia. Qed.

      Lemma fuelDecreases_min: forall dir min min' x x' b,
        min' < min -> progress dir x (Success (Some x')) -> fuelBound min x dir <= S b -> fuelBound min' x' dir <= b.
      Proof.
        intros. unfold fuelBound,MatchState.remainingChars in *. inversion H0; destruct dir; inversion H6; subst.
        - rewrite -> H3 in *. lia.
        - lia.
      Qed.

      Lemma fuelDecreases_progress: forall dir rer min x x' b,
        progress dir x (Success (Some x')) ->
        ((MatchState.endIndex x) =? (MatchState.endIndex x'))%Z = false ->
        MatchState.Valid (MatchState.input x) rer x ->
        MatchState.Valid (MatchState.input x) rer x' ->
        fuelBound min x dir <= S b ->
        fuelBound min x' dir <= b.
      Proof.
        intros dir rer min x x' b P_x_x' Neq_Eis [ ? [ [ Bei_x_l Bei_x_h ] VC_x ] ] [ ? [ [ B_Ei_x'_l B_Ei_x'_h ] VC_x' ] ] Ineq_fuel.
        dependent destruction P_x_x'. rename H into Eq_inp_x_x', H0 into Dp_x_x'.
        unfold fuelBound, MatchState.remainingChars in *.
        rewrite <- Eq_inp_x_x' in *.
        spec_reflector Z.eqb_spec.
        dependent destruction Dp_x_x'; lia.
      Qed.

      Lemma repeatMatcher': forall greedy parenIndex parenCount m rer dir,
        Captures.Valid rer parenIndex parenCount ->
        matcher_invariant m dir rer ->
        forall fuel min max,
          conditional_matcher_invariant (fun x => fuelBound min x dir <= fuel) (Definitions.RepeatMatcher.matcher m min max greedy parenIndex parenCount fuel) dir rer.
      Proof.
        intros greedy parenIndex parenCount m rer dir V_captures MI_m.
        induction fuel; intros min max x c Ineq_fuel V_x.
        - exfalso. unfold fuelBound,MatchState.remainingChars in Ineq_fuel. lia.
        - assert (forall caps indices res,
            List.Update.Nat.Batch.update undefined (MatchState.captures x) indices = Success caps ->
            m (match_state (MatchState.input x) (MatchState.endIndex x) caps) (Definitions.RepeatMatcher.continuation x c m min max greedy parenIndex parenCount fuel) = res ->
            res = failure \/
            (exists y : MatchState,
               MatchState.Valid (MatchState.input x) rer y /\
               progress dir x (Success (Some y)) /\ c y = res)
          ) as Ind. {
            intros caps indices res Eq_caps Matching.
            apply_mi MI_m in Matching as [ ? | (y0 & ? & ? & Matching) ] by MatchState.solve; [ search | ].
            unfold Definitions.RepeatMatcher.continuation in Matching.
            fold_matchers.
            focus <! _ [] _ !> auto destruct in Matching; [ search | ].
            unfold conditional_matcher_invariant in IHfuel.
            lazymatch type of Matching with 
            | _ _ ?n_min ?n_max _ _ _ _ ?y ?k = _ => specialize IHfuel with (min := n_min) (max := n_max) (x := y) (c := k)
            end.
            rewrite <- Matching. clear Matching.
            fforward IHfuel by try MatchState.solve.
            1: {
              destruct (min =?= 0).
              - subst. boolean_simplifier. quick_math. apply fuelDecreases_progress with (x := x) (rer := rer); try assumption. 
                + Progress.solve.
                + quick_math. easy.
              - rewrite <- EqDec.inversion_false in *. rewrite -> n. apply fuelDecreases_min with (x := x) (min := min); try assumption. 
                + rewrite -> EqDec.inversion_false in *. lia.
                + Progress.solve.
            }
            destruct IHfuel as [ ? | (y1 & V_y1 & P_y0_y1 & Eq_res) ]; search.
          }
          run matcher as Matching; try search.
          (* Most cases are 'just' a recursive call; use Ind *)
          1-6: fold_matchers; Result.inject_all; subst; eapply Ind; eassumption.
          + (* Capture reset failed due to OOB update => prove this actually cannot happen. *)
            ltac2:(retrieve (List.Update.Nat.Batch.update _ (MatchState.captures x) _ = Error _) as Falsum).
            apply List.Update.Nat.Batch.failure_bounds in Falsum.
            destruct V_x as [ _ [ _ [ VCL_x _ ]]]. rewrite -> VCL_x in *. repeat rewrite Nat.add_sub in *.
            unfold Captures.Valid in V_captures. contradiction.
      Qed.

      Lemma repeatMatcher: forall m min max greedy parenIndex parenCount dir rer,
        Captures.Valid rer parenIndex parenCount ->
        matcher_invariant m dir rer ->
        matcher_invariant (fun x c => repeatMatcher m min max greedy x c parenIndex parenCount) dir rer.
      Proof.
        intros m min max greedy parenIndex parenCount dir rer V_captures MI_m x c V_x.
        apply (repeatMatcher' _ _ _ _ _ _ V_captures MI_m (repeatMatcherFuel min x) _ _ x _ ltac:(cbn; eauto using repeatMatcherFuel_satisfies_bound) V_x).
      Qed.
    End RepeatMatcher.

    Section Lookaround.
      Lemma positiveLookaroundMatcher: forall m rer dir dir',
        matcher_invariant m dir' rer ->
        matcher_invariant (Definitions.PositiveLookaround.matcher m) dir rer.
      Proof.
        intros m rer dir dir' MI_m. unfold Definitions.PositiveLookaround.matcher.
        run matcher as Matching; autounfold with result_wrappers in *;
          match goal with | [ H: m _ _ = _ _ |- _ ] => rename H into Eq_m end.
        - search.
        - apply_mi MI_m in Eq_m as (? & ? & _ & [=->]) by assumption. search.
        - apply_mi MI_m in Eq_m as (? & ? & _ & [=->]) by assumption. search.
        - apply_mi MI_m in Eq_m as (? & _ & _ & ?) by assumption. discriminate.
      Qed.

      Lemma negativeLookaroundMatcher: forall m rer dir dir',
        matcher_invariant m dir' rer ->
        matcher_invariant (Definitions.NegativeLookaround.matcher m) dir rer.
      Proof.
        intros m rer dir dir' MI_m. unfold Definitions.NegativeLookaround.matcher.
        run matcher as Matching; autounfold with result_wrappers in *.
        - search.
        - search.
        - search.
        - match goal with | [ H: m _ _ = _ _ |- _ ] => rename H into Eq_m end.
          apply_mi MI_m in Eq_m as (? & _ & _ & ?) by assumption. discriminate.
      Qed.
    End Lookaround.

    Section Backreference.
      Lemma captured_range_diff: forall str rer x i r,
        MatchState.Valid str rer x ->
        List.Indexing.Nat.indexing (MatchState.captures x) i = Success (Some r) ->
        (0 <= (CaptureRange.endIndex r) - (CaptureRange.startIndex r))%Z.
      Proof. intros. MatchState.normalize. specialize (VCF_captures_x _ _ H0). dependent destruction VCF_captures_x. lia. Qed.

      Lemma backreferenceMatcher: forall rer n dir,
        (positive_to_non_neg n) <= RegExpRecord.capturingGroupsCount rer ->
        matcher_invariant (backreferenceMatcher rer n dir) dir rer.
      Proof.
        intros rer n dir Eq_rer. unfold backreferenceMatcher.
        run matcher as Matching; autounfold with result_wrappers in *.
        - search.
        - search.
        - search.
        - search.
          + destruct dir; cbn in *; MatchState.solve_with ltac:(cbn in *; lia).
          + apply Progress.step. eapply captured_range_diff; eassumption.
        - search.
        - search.
          + destruct dir; cbn in *; MatchState.solve_with ltac:(cbn in *; lia).
          + apply Progress.step. eapply captured_range_diff; eassumption.
        - (* An out-of-bound happend while indexing the input string: we prove it is actually impossible. *)
          injection Matching as ->.

          (* The maximal offset (r = endIndex - startIndex) is positive *)
          remember (CaptureRange.endIndex t - CaptureRange.startIndex t)%Z as r.
          assert (0 <= r)%Z as Pos_r. { subst r. eapply captured_range_diff; eassumption. }

          (* The end and start of the range and the current index, are in bounds *)
          destruct V_x as (_ & ? & _ & V_range).
          match goal with
          | [ H: List.Indexing.Nat.indexing (MatchState.captures x) _ = Success (Some _) |- _ ] =>
              specialize (V_range _ _ H); dependent destruction V_range
          end.
          unfold IteratorOn in *.

          (* Get rid of Z.min *)
          rewrite -> directional_min_rewrite  in * by assumption.

          (* There must be an offset i (0 <= i < r) where the indexing fails *)
          match goal with | [ H: List.Exists.exist _ _ = Error _ |- _ ] => rename H into Indexing_failure end.
          apply List.Exists.failure_kind in Indexing_failure.
          destruct Indexing_failure as [ i [ j [ Eq_indexed Indexing_failure ]]].
          pose proof (List.Range.Int.Bounds.indexing _ _ _ _ Eq_indexed) as ->. apply List.Indexing.Int.success_bounds in Eq_indexed.
          rewrite -> List.Range.Int.Bounds.length in *. cbn in *.

          (* Conclude by case analysis *)
          focus <! _ [] _ !> auto destruct in Indexing_failure; injection Indexing_failure as ->;
            match goal with
            | [ H: List.Indexing.Int.indexing _ _ = Error _ |- _ ] =>
                apply List.Indexing.Int.failure_bounds in H as [Indexing_failure | Indexing_failure]
            end; destruct dir.
          all: cbn in *; lia.
        - (* The capture group does not exist; we prove it is actually impossible. *)
          injection Matching as ->.
          match goal with | [ H: List.Indexing.Nat.indexing _ _ = Error _ |- _ ] => rename H into Eq_failure end.
          apply List.Indexing.Nat.failure_bounds in Eq_failure.
          destruct V_x as (_ & _ & ? & _). pose proof (NonNegInt.pos n). lia.
      Qed.
    End Backreference.

    Inductive Guard := guard.
    Ltac node_induction :=
      lazymatch goal with
      | [|- forall r ctx, Root ?root (r, ctx) -> @?P r ctx ] =>
          let P' := (eval cbn in (fun p => forall _: Guard, P (fst p) (snd p))) in
          let Tmp1 := fresh "r" in let Tmp2 := fresh "ctx" in let Tmp3 := fresh "Tmp" in 
          intros Tmp1 Tmp2 Tmp3; generalize guard; generalize dependent Tmp3; generalize dependent Tmp2; generalize dependent Tmp1;
          apply (Node_ind root P')
      end;
      repeat lazymatch goal with
      | [ H: Guard -> _ |- _ ] => specialize (H guard)
      | [|- forall a: Guard, _ ] => fail
      | [|- forall (_: ?T), _ ] => match type of T with
        | Prop => let H := fresh "IH" in intros H
        | _ => intros ?
        end
      end; intros _.

    Ltac compileSubPattern_helper := repeat match goal with
    | [ IH: forall _ _, compileSubPattern ?r _ _ _ = Success _ -> _, H: compileSubPattern ?r _ _ _ = Success _  |- _ ] =>
        specialize IH with (1 := H)
    end.

    Lemma isWordChar_failure: forall rer x f, isWordChar rer (MatchState.input x) (MatchState.endIndex x) = Error f -> ~ MatchState.Valid (MatchState.input x) rer x.
    Proof.
      unfold isWordChar. cbn. intros rer x f H Falsum.
      focus <! _ [] _ !> auto destruct in H. ltac2:(retrieve (List.Indexing.Int.indexing _ _ = Error _) as H').
      apply List.Indexing.Int.failure_bounds in H'. quick_math. MatchState.solve_with lia.
    Qed.
    Lemma isWordChar_failure_min: forall rer x f, isWordChar rer (MatchState.input x) (MatchState.endIndex x - 1)%Z = Error f -> ~ MatchState.Valid (MatchState.input x) rer x.
    Proof.
      unfold isWordChar. cbn. intros rer x f H Falsum.
      focus <! _ [] _ !> auto destruct in H. ltac2:(retrieve (List.Indexing.Int.indexing _ _ = Error _) as H').
      apply List.Indexing.Int.failure_bounds in H'. quick_math. MatchState.solve_with lia.
    Qed.

    Ltac pinpoint_failure := repeat match goal with
      | [ H: _ = Error _ |- _ ] => progress (focus <! _ [] _ !> auto destruct in H); injection H as ->
      | [ H: List.Update.Nat.One.update _ _ _ = Error _ |- _ ] => apply List.Update.Nat.One.failure_bounds in H
      | [ H: List.Indexing.Int.indexing _ _ = Error _ |- _ ] => apply List.Indexing.Int.failure_bounds in H
      | [ H: isWordChar _ _ _ = Error _ |- _ ] => apply isWordChar_failure in H + apply isWordChar_failure_min in H
      end.

    Lemma compileSubPattern: forall root rer,
      countLeftCapturingParensWithin root nil = RegExpRecord.capturingGroupsCount rer ->
      EarlyErrors.Pass_Regex root nil ->
      forall r ctx,
      Root root (r, ctx) ->
      forall  dir m,
      compileSubPattern r ctx rer dir = Success m ->
      matcher_invariant m dir rer.
    Proof.
      intros root rer Eq_rer EE_root.
      node_induction.
      all: intros dir m Eq_m; cbn -[Semantics.repeatMatcher] in Eq_m.
      - (* Empty *)
        injection Eq_m as <-. intros x c V_x. right. exists x. split_conjs; [ assumption | Progress.solve | reflexivity ].
      - (* Character *)
        injection Eq_m as <-. apply characterSetMatcher.
      - (* Dot *)
        injection Eq_m as <-. apply characterSetMatcher.
      - (* AtomEscape *)
        destruct ae.
        + (* Numbered backref *)
          focus <! _ [] _ !> auto destruct in Eq_m; injection Eq_m as <-.
          apply backreferenceMatcher. quick_math. assumption.
        + (* Character class *)
          destruct esc; focus <! _ [] _ !> auto destruct in Eq_m; injection Eq_m as <-; apply characterSetMatcher.
        + (* Character *)
          destruct esc; focus <! _ [] _ !> auto destruct in Eq_m; injection Eq_m as <-; apply characterSetMatcher.
        + (* Named backref *)
          focus <! _ [] _ !> auto destruct in Eq_m; injection Eq_m as <-.
          ltac2:(retrieve (List.Unique.unique _ = Success _) as H0).
          ltac2:(retrieve (NonNegInt.to_positive _ = Success _) as H1).
          apply backreferenceMatcher. quick_math. cbn in *.
          apply List.Unique.success in H0. destruct s. cbn in *.
          assert (List.Indexing.Nat.indexing (groupSpecifiersThatMatch (AtomEsc (GroupEsc id)) ctx id) 0 = Success (r, l)) as Eq_indexed. {
            match goal with | [ H: _ = (r, l) :: nil |- _ ] => setoid_rewrite -> H end.
            reflexivity.
          }
          pose proof (EarlyErrors.groupSpecifiersThatMatch_is_filter_map (AtomEsc (GroupEsc id)) ctx id) as (f & _ & Def_f).
          apply Def_f in Eq_indexed. destruct Eq_indexed as (ctx' & ? & Eq_indexed).
          subst. destruct (countLeftCapturingParensBefore_impl ctx' + 1) eqn:Eq; try lia. cbn in *.
          apply Zipper.Walk.soundness in Eq_indexed. eapply Zipper.Down.same_root_down in Eq_indexed; [ | eapply IH ]. cbn in *.
          pose proof (EarlyErrors.countLeftCapturingParensBefore_contextualized _ _ _ Eq_indexed EE_root).
          subst. unfold countLeftCapturingParensBefore,countLeftCapturingParensWithin in *. cbn in *.
          apply NonNegInt.to_positive_soundness in H1.
          lia.
      - (* Character class *)
        focus <! _ [] _ !> auto destruct in Eq_m; auto using Compile.compileCharacterClass.
        injection Eq_m as <-. apply characterSetMatcher.
      - (* Disjunction *)
        focus <! _ [] _ !> auto destruct in Eq_m. injection Eq_m as <-.
        compileSubPattern_helper.
        run matcher as Matching; try ltac2:(retrieve (s _ _ = _) as H0); rewrite <- Matching, <- ?H0 in *; auto.
      - (* Quantifier *)
        focus <! _ [] _ !> auto destruct in Eq_m. injection Eq_m as <-. apply repeatMatcher.
        + intros i v Eq_indexed.
          pose proof (List.Indexing.Nat.success_bounds _ _ _ Eq_indexed). rewrite -> List.Range.Nat.Bounds.length in *.
          apply List.Range.Nat.Bounds.indexing in Eq_indexed.
          pose proof (EarlyErrors.countLeftCapturingParensBefore_contextualized _ _ _ IH EE_root).
          unfold countLeftCapturingParensBefore,countLeftCapturingParensWithin in *. cbn in *. lia.
        + compileSubPattern_helper. assumption.
      - (* Sequence *)
        destruct dir; cbn in *.
        + focus <! _ [] _ !> auto destruct in Eq_m. injection Eq_m as <-.
          compileSubPattern_helper.
          run matcher as Matching; rewrite <- Matching.
          * apply_mi IH0 by assumption. apply_mi IH2 by MatchState.solve. right. search. Progress.normalize. lia.
          * apply_mi IH0 by assumption. apply_mi IH2 by MatchState.solve. right. search. Progress.normalize. lia.
        + focus <! _ [] _ !> auto destruct in Eq_m. injection Eq_m as <-.
          compileSubPattern_helper.
          run matcher as Matching; rewrite <- Matching.
          * apply_mi IH2 by assumption. apply_mi IH0 by MatchState.solve. right. search. Progress.normalize. lia.
          * apply_mi IH2 by assumption. apply_mi IH0 by MatchState.solve. right. search. Progress.normalize. lia.
      - (* (Capturing) Group *)
        focus <! _ [] _ !> auto destruct in Eq_m. injection Eq_m as <-.
        compileSubPattern_helper.
        run matcher as Matching.
        + (* Run succeeded *)
          apply_mi IH0 in Matching as [? | (y & V_y & P_y & Eq_s)] by assumption.
          * subst. left. reflexivity.
          * focus <! _ [] _ !> auto destruct in Eq_s.
            ltac2:(retrieve ((if _ then _ else _) = Success _) as H0).
            focus <! _ [] _ !> auto destruct in H0.
            search.
        + (* Error occured => toward contradiction *)
          apply_mi IH0 in Matching as (y & V_y & P_y & Eq_f) by assumption.
          focus <! _ [] _ !> auto destruct in Eq_f.
          * (* Cause: call to continuation *)
            match goal with | [ H: _ = Success ?s |- _ ] => check_type s (list (option CaptureRange)); focus <! _ [] _ !> auto destruct in H end.
            search.
          * (* Cause: capture update *)
            injection Eq_f as ->.
            match goal with | [ H: _ = Error ?f |- _ ] => focus <! _ [] _ !> auto destruct in H end.
            -- (* Count left paren is -1 *)
                quick_math. lia.
            -- (* Update oob *)
               pinpoint_failure.
               pose proof (countLeftCapturingParensBefore_contextualized ctx _ _ ltac:(eassumption) ltac:(eassumption)).
               destruct V_y as (_ & _ & Tmp & _); rewrite <- Tmp in *. rewrite <- Eq_rer in *. unfold countLeftCapturingParensWithin,countLeftCapturingParensBefore in *. cbn in *.
               MatchState.solve_with lia.
          * (* Cause: invalid range *)
            injection Eq_f as ->.
            lazymatch goal with | [ H: _ = Error _ |- _ ] => destruct dir; focus <! _ [] _ !> auto destruct in H; injection H as <- end. 
            all: boolean_simplifier; quick_math; Progress.normalize; lia.
      - (* Match start *)
        injection Eq_m as <-. run matcher as Matching; try search.
        injection Matching as ->.
        pinpoint_failure.
        MatchState.solve_with lia.
      - (* Match end *)
        injection Eq_m as <-. run matcher as Matching; try search.
        injection Matching as ->.
        pinpoint_failure.
        MatchState.solve_with lia.
      - (* Word boundary *)
        injection Eq_m as <-. run matcher as Matching; try search; injection Matching as <-; pinpoint_failure; contradiction.
      - (* Non word boundary *)
        injection Eq_m as <-. run matcher as Matching; try search; injection Matching as <-; pinpoint_failure; contradiction.
      - (* Lookahead *)
        focus <! _ [] _ !> auto destruct in Eq_m. injection Eq_m as <-. apply positiveLookaroundMatcher with (dir' := forward). auto.
      - (* Negative lookahead *)
        focus <! _ [] _ !> auto destruct in Eq_m. injection Eq_m as <-. apply negativeLookaroundMatcher with (dir' := forward). auto.
      - (* Lookbehind *)
        focus <! _ [] _ !> auto destruct in Eq_m. injection Eq_m as <-. apply positiveLookaroundMatcher with (dir' := backward). auto.
      - (* Negative lookbehind *)
        focus <! _ [] _ !> auto destruct in Eq_m. injection Eq_m as <-. apply negativeLookaroundMatcher with (dir' := backward). auto.
    Qed.
  End main. End MatcherInvariant.

  (** We can now show the core properties of the spec. *)

  (* The initial state generated by compilePattern is always valid (under mild assumptions) *)
  Lemma initialState_validity `{Parameters}: forall input i rer,
    i <= (length input) ->
    MatchState.Valid input rer (match_state input (Z.of_nat i) (repeat None (RegExpRecord.capturingGroupsCount rer))).
  Proof.
    constructor.
    + subst. MatchState.solve.
    + subst. split_conjs.
      * subst. cbn. constructor; lia.
      * cbn. rewrite -> List.repeat_length. reflexivity.
      * intros j v Indexed.
        cbn in Indexed. apply List.Indexing.Nat.repeat in Indexed. subst.
        constructor.
  Qed.

  (** Monotony: when a match is found, its end position is always greater than the starting point. *)
  Theorem monotony `{Parameters}: forall r rer input i m,
    EarlyErrors.Pass_Regex r nil ->
    countLeftCapturingParensWithin r nil = RegExpRecord.capturingGroupsCount rer ->
    compilePattern r rer = Success m ->
    progress forward (match_state input (Z.of_nat i) (List.repeat None (RegExpRecord.capturingGroupsCount rer))) (m input i).
  Proof.
    intros r rer input i m EE_root Eq_rer Eq_m.
    unfold compilePattern in *.
    focus <! _ [] _ !> auto destruct in Eq_m. injection Eq_m as <-. ltac2:(retrieve (compileSubPattern r _ _ _ = Success _) as H0).
    cbn. focus <! _ _ _ [] !> auto destruct.
    - constructor.
    - boolean_simplifier. spec_reflector Nat.leb_spec0.
      (* Assert that the start state is valid *)
      focus <! _ _ [] _ !> remember as x with equality Eq_x.
      assert (MatchState.Valid (MatchState.input x) rer x) as V_x. {
        subst. apply initialState_validity. assumption.
      }
      (* Use the matcher invariant *)
      pose proof (MatcherInvariant.compileSubPattern) as G.
      specialize G with (1 := Eq_rer) (2 := EE_root) (3 := ltac:(apply Zipper.Root.id)) (4 := H0).
      specialize (G x (fun y => y) V_x).
      (* Match either failed or succeeded *)
      destruct G as [ -> | (y & ? & ? & <-) ].
      + (* Error => vacuously true *)
        constructor.
      + (* Success => Direct from matcher invariant *)
        Progress.solve.
  Qed.

  (* Another variant, which doesn't use progress *)
  Theorem monotony' `{Parameters}: forall r rer input i m z,
    EarlyErrors.Pass_Regex r nil ->
    countLeftCapturingParensWithin r nil = RegExpRecord.capturingGroupsCount rer ->
    compilePattern r rer = Success m ->
    m input i = Success (Some z) ->
    (Z.of_nat i <= MatchState.endIndex z)%Z.
  Proof.
    intros r rer input i m z EE_r Eq_rer Eq_m Eq_z.
    pose proof (monotony r rer input i m EE_r Eq_rer Eq_m) as P.
    dependent destruction P; autounfold with result_wrappers in *; try congruence.
    dependent destruction H1.
    cbn in *. rewrite -> Eq_z in *. injection x as [=->]. assumption.
  Qed.

  (** Termination: the matching process never runs out of fuel, i.e. out_of_fuel is never returned *)
  Theorem termination `{Parameters}: forall r rer input i m,
    EarlyErrors.Pass_Regex r nil ->
    countLeftCapturingParensWithin r nil = RegExpRecord.capturingGroupsCount rer ->
    compilePattern r rer = Success m ->
    (m input i) <> out_of_fuel.
  Proof.
    intros r rer input i m EE_root Eq_rer Eq_m.
    unfold compilePattern in *.
    focus <! _ [] _ !> auto destruct in Eq_m. injection Eq_m as <-. ltac2:(retrieve (compileSubPattern r _ _ _ = Success _) as H0).
    cbn. focus <! _ (_ [] _) !> auto destruct.
    boolean_simplifier. spec_reflector Nat.leb_spec0.
    (* Assert that the start state is valid *)
    focus <! _ (_ (_ [] _) _) !> remember as x with equality Eq_x.
    assert (MatchState.Valid (MatchState.input x) rer x) as V_x. {
      subst. apply initialState_validity. assumption.
    }
    (* Use the matcher invariant *)
    pose proof (MatcherInvariant.compileSubPattern) as G.
    specialize G with (1 := Eq_rer) (2 := EE_root) (3 := ltac:(apply Zipper.Root.id)) (4 := H0).
    specialize (G x (fun y => y) V_x).
    (* Match either failed or succeeded *)
    destruct G as [ -> | (y & ? & ? & <-) ].
    + (* Error => vacuously true *)
      easy.
    + (* Success => contradiction, due to continuation *)
      easy.
  Qed.

  (** No failure: no assertion is ever triggered, and no unspecified behavior occurs, i.e. match_assertion_failed is never returned *)
  Theorem no_failure `{Parameters}: forall r rer input i m,
    EarlyErrors.Pass_Regex r nil ->
    countLeftCapturingParensWithin r nil = RegExpRecord.capturingGroupsCount rer ->
    compilePattern r rer = Success m ->
    (i <= length input) ->
    (m input i) <> match_assertion_failed.
  Proof.
    intros r rer input i m EE_root Eq_rer Eq_m Bound_i.
    unfold compilePattern in *.
    focus <! _ [] _ !> auto destruct in Eq_m. injection Eq_m as <-. ltac2:(retrieve (compileSubPattern r _ _ _ = Success _) as H0).
    cbn. focus <! _ (_ [] _) !> auto destruct.
    - boolean_simplifier. spec_reflector Nat.leb_spec0. lia.
    - boolean_simplifier. spec_reflector Nat.leb_spec0.
      (* Assert that the start state is valid *)
      focus <! _ (_ (_ [] _) _) !> remember as x with equality Eq_x.
      assert (MatchState.Valid (MatchState.input x) rer x) as V_x. {
        subst. apply initialState_validity. assumption.
      }
      (* Use the matcher invariant *)
      pose proof (MatcherInvariant.compileSubPattern) as G.
      specialize G with (1 := Eq_rer) (2 := EE_root) (3 := ltac:(apply Zipper.Root.id)) (4 := H0).
      specialize (G x (fun y => y) V_x).
      (* Match either failed or succeeded *)
      destruct G as [ -> | (y & ? & ? & <-) ].
      + (* Error => vacuously true *)
        easy.
      + (* Success => contradiction, due to continuation *)
        easy.
  Qed.
End Correctness.
