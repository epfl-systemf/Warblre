(* From Coq Require Import Strings.String Structures.Orders Lia Program.Subset MSets FMaps. *)
From Coq Require Import PeanoNat Bool Lia.
From Warblre Require Import Tactics Result Base Patterns StaticSemantics Notation.

Import Result.Notations.
Local Open Scope result_flow.

(** 22.2.2.2 Runtime Semantics: CompilePattern *)
Module Semantics.
  Import Patterns.
  Import Notation.


  (** 22.2.2.3.1 RepeatMatcher ( m, min, max, greedy, x, c, parenIndex, parenCount ) *)
  Fixpoint repeatMatcher' (m: Matcher) (min: non_neg_integer) (max: non_neg_integer_or_inf) (greedy: bool) (x: MatchState) (c: MatcherContinuation) (groupsWithin: IdSet.t) (fuel: nat): MatchResult :=
  (* Coq wants to make sure the function will terminate; we do so by bounding recursion by an arbitrary fuel amount *)
  match fuel with
  | 0 => out_of_fuel
  | S fuel' =>
    (* 1. If max = 0, return c(x). *)
    if max is (Some 0) then c x else
    (* 2. Let d be a new MatcherContinuation with parameters (y) that captures m, min, max, greedy, x, c, parenIndex, and parenCount and performs the following steps when called: *)
    let d := fun (y: MatchState) =>
      (* a. Assert: y is a MatchState. *)
      (* b. If min = 0 and y's endIndex = x's endIndex, return failure. *)
      if (Nat.eqb min 0) && (Nat.eqb (MatchState.endIndex y) (MatchState.endIndex x)) 
        then failure else
      (* c. If min = 0, let min2 be 0; otherwise let min2 be min - 1. *)
      let min2 :=
        if Nat.eqb min 0 then 0
        else min - 1
      in
      (* TODO: improve *)
      (* d. If max = +∞, let max2 be +∞; otherwise let max2 be max - 1. *)
      let max2 := match max with
        | None => +∞
        | Some n => Some (n -1)
      end in
      (* e. Return RepeatMatcher(m, min2, max2, greedy, y, c, parenIndex, parenCount). *)
      repeatMatcher' m min2 max2 greedy y c groupsWithin fuel'
    in
    (* 3. Let cap be a copy of x's captures List. *)
    let cap := MatchState.captures x in
    (* 4. For each integer k in the inclusive interval from parenIndex + 1 to parenIndex + parenCount, set cap[k] to undefined. *)
    let cap := IdSet.fold DMap.remove groupsWithin cap in
    (* 5. Let Input be x's input. *)
    let input := MatchState.input x in
    (* 6. Let e be x's endIndex. *)
    let e := MatchState.endIndex x in
    (* 7. Let xr be the MatchState (Input, e, cap). *)
    let xr := MatchState.make input e cap in
    (* 8. If min ≠ 0, return m(xr, d). *)
    if negb (Nat.eqb min 0) 
      then m xr d else
    (* 9. If greedy is false, then *)
    if greedy is false then
      (* a. Let z be c(x). *)
      let z := c x in
      (* b. If z is not failure, return z. *)
      if z is not failure then z else
      (* c. Return m(xr, d).*)
      m xr d
    else
    (* 10. Let z be m(xr, d). *)
    let z := m xr d in
    (* 11. If z is not failure, return z. *)
    if z is not failure then z else
    (* 12. Return c(x). *)
    c x
  end.
  Definition repeatMatcher (m: Matcher) (min: non_neg_integer) (max: non_neg_integer_or_inf) (greedy: bool) (x: MatchState) (c: MatcherContinuation) (groupsWithin: IdSet.t): MatchResult :=
    repeatMatcher' m min max greedy x c groupsWithin (min + length (MatchState.input x) + 1).

  Fixpoint compileSubPattern (self: Regex) (rer: RegExp) (direction: direction): Matcher := match self with
  | Char A invert =>  (** 7.1 CharacterSetMatcher ( rer, A, invert, direction ) *)
                      (* 1. Return a new Matcher with parameters (x, c) that captures rer, A, invert, and direction and performs the following steps when called: *)
                      (* a. Assert: x is a MatchState. *)
                      (* b. Assert: c is a MatcherContinuation. *)
                      fun (x: MatchState) (c: MatcherContinuation) =>
                        (* c. Let Input be x's input. *)
                        let input := MatchState.input x in
                        (* d. Let e be x's endIndex. *)
                        let e := MatchState.endIndex x in
                        let f :=
                          (* e. If direction is forward, let f be e + 1. *)
                          if Direction.eqb direction forward
                          then e + 1
                          (* f. Else, let f be e - 1. *)
                          else e - 1
                        in
                        (* g. Let InputLength be the number of elements in Input. *)
                        let inputLength := length input in
                        (* h. If f < 0 or f > InputLength, return failure. *)
                        if (Nat.leb f 0) || (Nat.leb (S inputLength) f) then
                          failure
                        else
                          (* i. Let index be min(e, f). *)
                          let index := min e f in
                          (* j. Let ch be the character Input[index]. *)
                          let! chr <- input[ index ] in
                          (* k. Let cc be Canonicalize(rer, ch). *)
                          let cc := chr in
                          (* l. If there exists a member a of A such that Canonicalize(rer, a) is cc, let found be true. Otherwise, let found be false. *)
                          let found := A cc in
                          (* m. If invert is false and found is false, return failure. *)
                          if Bool.eqb invert false && Bool.eqb found false then
                            failure
                          (* n. If invert is true and found is true, return failure. *)
                          else if Bool.eqb invert true && Bool.eqb found true then
                            failure
                          else
                            (* o. Let cap be x's captures List. *)
                            let cap := MatchState.captures x in
                            (* p. Let y be the MatchState (Input, f, cap). *)
                            let y := match_state input f cap in
                            (* q. Return c(y). *)
                            c y
  | Disjunction r1 r2 =>
                      (* 1. Let m1 be CompileSubpattern of Alternative with arguments rer and direction. *)
                      let m1 := compileSubPattern r1 rer direction in
                      (* 2. Let m2 be CompileSubpattern of Disjunction with arguments rer and direction. *)
                      let m2 := compileSubPattern r2 rer direction in
                      (* 3. Return a new Matcher with parameters (x, c) that captures m1 and m2 and performs the following steps when called: *)
                      (* a. Assert: x is a MatchState. *)
                      (* b. Assert: x is a MatchState. *)
                      fun (x: MatchState) (c: MatcherContinuation) =>
                        (* c. Let r be m1(x, c). *)
                        let r := m1 x c in
                        (* d. If r is not failure, return r. *)
                        if r is not failure then
                          r
                        else
                          (* e. Return m2(x, c). *)
                          m2 x c
  | Kleene r      =>  let m := compileSubPattern r rer direction in
                      let groups := capturingGroupsWithin r in
                      fun (x: MatchState) (c: MatcherContinuation) =>
                        repeatMatcher m 0 +∞ true x c groups 
  | Seq r1 r2     =>  (**  Alternative :: Alternative Term *)
                      (* 1. Let m1 be CompileSubpattern of Alternative with arguments rer and direction. *)
                      let m1 := compileSubPattern r1 rer direction in
                      (* 2. Let m2 be CompileSubpattern of Term with arguments rer and direction. *)
                      let m2 := compileSubPattern r2 rer direction in
                      (* 3. If direction is forward, then *)
                      if direction is forward then
                        (* a. Return a new Matcher with parameters (x, c) that captures m1 and m2 and performs the following steps when called: *)
                        (* i. Assert: x is a MatchState. *)
                        (* ii. Assert: c is a MatcherContinuation. *)
                        fun (s: MatchState) (c: MatcherContinuation) =>
                          (* iii. Let d be a new MatcherContinuation with parameters (y) that captures c and m2 and performs the following steps when called: *)
                          (* 1. Assert: y is a MatchState. *)
                          let d := fun (s: MatchState) => 
                            (* 2. Return m2(y, c). *)
                            m2 s c
                          in
                          (* iv. Return m1(x, d). *)
                          m1 s d
                      (* 4. Else, *)
                      else
                        (* a. Assert: direction is backward. *)
                        (* b. Return a new Matcher with parameters (x, c) that captures m1 and m2 and performs the following steps when called: *)
                        (* i. Assert: x is a MatchState. *)
                        (* ii. Assert: x is a MatchState. *)
                        fun (s: MatchState) (c: MatcherContinuation) =>
                          (* iii. Let d be a new MatcherContinuation with parameters (y) that captures c and m1 and performs the following steps when called: *)
                          (* 1. Assert: y is a MatchState. *)
                          let d := fun (s: MatchState) =>
                            (* Return m1(y, c). *)
                            m1 s c 
                          in
                          (* iv. Return m2(x, d). *)
                          m2 s d
  | Group id r    =>  (**  Atom :: ( GroupSpecifier_opt Disjunction ) *)
                      (* 1. Atom :: ( GroupSpecifieropt Disjunction ) *)
                      let m := compileSubPattern r rer direction in
                      (* 2. Let parenIndex be CountLeftCapturingParensBefore(Atom). *)
                      let parenIndex := id in
                      (* 3. Return a new Matcher with parameters (x, c) that captures direction, m, and parenIndex and performs the following steps when called: *)
                      (* a. Assert: x is a MatchState. *)
                      (* b. Assert: c is a MatcherContinuation. *)
                      fun (x: MatchState) (c: MatcherContinuation) => 
                        (* c. Let d be a new MatcherContinuation with parameters (y) that captures x, c, direction, and parenIndex and performs the following steps when called: *)
                        (* i. Assert: y is a MatchState. *)
                        let d := fun (y: MatchState) => 
                          (* ii. Let cap be a copy of y's captures List. *)
                          let cap := MatchState.captures y in
                          (* iii. Let Input be x's input. *)
                          let input := MatchState.input x in
                          (* iv. Let xe be x's endIndex. *)
                          let xe := MatchState.endIndex x in
                          (* v. Let ye be y's endIndex. *)
                          let ye := MatchState.endIndex y in
                          let! r <-
                            (* vi. If direction is forward, then *)
                            if direction is forward then
                              (* 1. Assert: xe ≤ ye. *)
                              assert! PeanoNat.Nat.leb xe ye ;
                              (* 2. Let r be the CaptureRange (xe, ye). *)
                              Success (CaptureRange.make xe ye)
                            (* vii. Else, *)
                            else
                              (* 1. Assert: direction is backward. *)
                              assert! direction is backward ;
                              (* 2. Assert: ye ≤ xe. *)
                              assert! PeanoNat.Nat.leb ye xe ;
                              (* 3. Let r be the CaptureRange (ye, xe). *)
                              Success (CaptureRange.make ye xe)
                          in
                          (* viii. Set cap[parenIndex + 1] to r. *)
                          let cap := DMap.add id r cap in
                          (* ix. Let z be the MatchState (Input, ye, cap). *)
                          let z := match_state input ye cap in
                          (* x. Return c(z). *)
                          c z
                        in
                        (* d. Return m(x, d). *)
                        m x d
  | Lookback r    =>  (**  Assertion :: (?<= Disjunction ) *)
                      (* 1. Let m be CompileSubpattern of Disjunction with arguments rer and backward. *)
                      let m := compileSubPattern r rer backward in
                      (* 2. Return a new Matcher with parameters (x, c) that captures m and performs the following steps when called: *)
                      (* a. Assert: x is a MatchState. *)
                      (* b. Assert: c is a MatcherContinuation. *)
                      fun (x: MatchState) (c: MatcherContinuation) =>
                        (* c. Let d be a new MatcherContinuation with parameters (y) that captures nothing and performs the following steps when called: *)
                        (* i. Assert: y is a MatchState. *)
                        let d := fun (y: MatchState) =>
                          (* ii. Return y. *)
                          Success y
                        in
                        (* d. Let r be m(x, d). *)
                        let r := m x d in
                        (* e. If r is failure, return failure. *)
                        if r is failure then
                          failure
                        else
                          (* f. Let y be r's MatchState. *)
                          destruct! Success y <- r ;
                          (* g. Let cap be y's captures List. *)
                          let cap := MatchState.captures y in
                          (* h. Let cap be y's captures List. *)
                          let input := MatchState.input x in
                          (* i. Let cap be y's captures List. *)
                          let xe := MatchState.endIndex x in
                          (* j. Let z be the MatchState (Input, xe, cap). *)
                          let z := match_state input xe cap in
                          (* k. Let z be the MatchState (Input, xe, cap). *)
                          c z
  end.

  Definition compilePattern (r: Regex) (rer: RegExp): list Character -> non_neg_integer -> MatchResult :=
    (* 1. Let m be CompileSubpattern of Disjunction with arguments rer and forward. *)
    let m := compileSubPattern r rer forward in
    (* 2. Return a new Abstract Closure with parameters (Input, index) that captures rer and m and performs the following steps when called: *)
    (* a. Assert: Input is a List of characters. *)
    fun (input: list Character) (index: non_neg_integer) =>
      (* Assert: 0 ≤ index ≤ the number of elements in Input. *)
      assert! PeanoNat.Nat.leb 0 index && PeanoNat.Nat.leb index (length input) ;
      (* c. Let c be a new MatcherContinuation with parameters (y) that captures nothing and performs the following steps when called: *)
      (* i. Assert: y is a MatchState. *)
      let c := fun (y: MatchState) =>
        (* Return y. *)
        Success y 
      in
      (* d. Let cap be a List of rer.[[CapturingGroupsCount]] undefined values, indexed 1 through rer.[[CapturingGroupsCount]]. *)
      let cap := DMap.empty CaptureRange.type in
      (* e. Let x be the MatchState (Input, index, cap). *)
      let x := match_state input index cap in
      (* f. Return m(x, c). *)
      m x c
    .

  (** Correctness proofs *)

  Inductive directionalProgress: direction -> MatchState -> MatchState -> Prop :=
  | dpForward: forall x y, le (MatchState.endIndex x) (MatchState.endIndex y) -> directionalProgress forward x y
  | dpBackward: forall x y, ge (MatchState.endIndex x) (MatchState.endIndex y) -> directionalProgress backward x y
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

  Ltac saturate_transitive rel trans := repeat match goal with
    | [ R1: rel ?S ?T, R2: rel ?T ?U |- _ ] => lazymatch goal with
      |  [ _ : rel S U |- _ ] => fail
      | [ |- _ ] => pose proof (trans S T U R1 R2)
      end
    end; try assumption.

  Ltac destruct_dps := repeat lazymatch goal with
  | [ H: directionalProgress ?d _ _ |- _ ] => is_constructor d; inversion H; clear H
  end.

  Lemma progress_refl: forall dir x, (progress dir) x (Success x).
  Proof. intros. destruct dir; constructor; try reflexivity; constructor; unfold ">="; apply Nat.le_refl. Qed.

  Lemma progress_trans: forall dir x y z, (progress dir) x (Success y) -> (progress dir) y z -> (progress dir) x z.
  Proof.
    intros.
    repeat match goal with
    | [ H: (progress _) _ (Success _) |- _ ] => inversion H; clear H; subst

    | [ |- (progress _) _ ?y ] => is_var y; let Eq := fresh "Eq" y in destruct y eqn:Eq
    | [ |- (progress _) _ ?y ] => constructor
    end.
    - congruence.
    - destruct dir; destruct_dps; constructor; unfold ">=" in *; saturate_transitive le Nat.le_trans.
  Qed.

  Lemma progress_ignores_captures: forall dir x y cx cy,
        (progress dir) x (Success y) 
    ->  (progress dir) 
          (match_state (MatchState.input x) (MatchState.endIndex x) cx)
          (Success (match_state (MatchState.input y) (MatchState.endIndex y) cy)).
  Proof. intros. inversion H. constructor; simpl.
    - assumption.
    - destruct dir; destruct_dps; constructor; assumption.
  Qed.

  Definition MonotonousContinuation (dir: direction) (c: MatcherContinuation) := forall x, (progress dir) x (c x).
  Definition MonotonousMatcher (dir: direction) (m: Matcher) := forall x c, (MonotonousContinuation dir) c -> (progress dir) x (m x c).
  #[export]
  Hint Transparent MonotonousContinuation MonotonousMatcher : core.

  Lemma matcher_to_continuation: forall dir m c, MonotonousMatcher dir m -> MonotonousContinuation dir c 
    -> MonotonousContinuation dir (fun (x: MatchState) => m x c).
  Proof. intros. unfold MonotonousContinuation. intros. apply H. assumption. Qed.

  Lemma repeatMatcher'_preserves_monotony_helper: forall dir x c fuel m min max greedy groupsWithin, 
    MonotonousMatcher dir m ->
    MonotonousContinuation dir c ->
    (forall (m : Matcher) (min : non_neg_integer)
         (max : non_neg_integer_or_inf) (greedy : bool)
         (groupsWithin : IdSet.t),
       MonotonousMatcher dir m ->
       MonotonousMatcher dir
         (fun (x : MatchState) (c : MatcherContinuation) =>
          repeatMatcher' m min max greedy x c groupsWithin fuel)) ->
    (progress dir) x
      (m
         (match_state (MatchState.input x) (MatchState.endIndex x)
            (IdSet.fold DMap.remove groupsWithin (MatchState.captures x)))
         (fun y : MatchState =>
          if Nat.eqb min 0 && Nat.eqb (MatchState.endIndex y) (MatchState.endIndex x)
          then failure
          else
           repeatMatcher' m (if Nat.eqb min 0 then 0 else min - 1)
             match max with
             | Some n => Some (n - 1)
             | None => +∞
             end greedy y c groupsWithin fuel)).
  Proof.
    intros.
    match goal with | [ |- (progress dir) x ?e ] => destruct e eqn:Eq end; try now constructor.
    remember (match_state (MatchState.input x) (MatchState.endIndex x) (IdSet.fold DMap.remove groupsWithin (MatchState.captures x))) as x'.
    apply progress_trans with (y := x').
    - subst. simpl. 
      replace x with (match_state (MatchState.input x) (MatchState.endIndex x) (MatchState.captures x)) at 1 by (destruct x; reflexivity).
      apply progress_ignores_captures. apply progress_refl.
    - rewrite <- Eq. apply H.
      unfold MonotonousContinuation. intros x0.
      repeat match goal with
      | [ |- (progress _) _ (if ?b then _ else _) ] => destruct b
      end; try now constructor. apply H1; assumption.
  Qed.

  Lemma repeatMatcher'_preserves_monotony: forall fuel dir m min max greedy groupsWithin, (MonotonousMatcher dir) m -> (MonotonousMatcher dir) (fun x c => repeatMatcher' m min max greedy x c groupsWithin fuel).
  Proof.
    intros fuel. induction fuel; intros; unfold MonotonousMatcher; intros; simpl; try now constructor.
    repeat match goal with
    | [ |- (progress dir) _ (if ?b then _ else _) ] => destruct b
    end.
    all: solve [ auto | apply repeatMatcher'_preserves_monotony_helper; try easy; intros; apply IHfuel; assumption ].
  Qed.

  Lemma repeatMatcher_preserves_monotony: forall dir m min max greedy groupsWithin, (MonotonousMatcher dir) m -> (MonotonousMatcher dir) (fun x c => repeatMatcher m min max greedy x c groupsWithin).
  Proof. intros. unfold repeatMatcher. epose proof (repeatMatcher'_preserves_monotony _ dir m min max greedy groupsWithin). admit.
  Admitted.

  Ltac remember_progress_target As := match goal with
  | [ |- (progress _) _ ?y ] => let Eq := fresh "Eq" As in remember y as As
  end.

  (* Sounds good, doesn't work *)
  Ltac remember_goal_part pat x As := idtac pat; match goal with
  | [ |- pat ] => idtac x; remember x as A
  end.
  Tactic Notation "tmp" ident(x) "of" uconstr(pat) "as" simple_intropattern(As) := remember_goal_part pat x As.

  Tactic Notation "delta" reference(id) := cbv delta [ id ].
  Tactic Notation "delta" reference(id) "in" hyp(h) := cbv delta [ id ] in h.

  Lemma compileSubpattern_result_is_monotonous: forall r rer dir, MonotonousMatcher dir (compileSubPattern r rer dir).
  Proof.
    induction r.
    - delta MonotonousMatcher. cbn. intros.
      repeat match goal with
      | [ |- (progress _) _ (if ?b then _ else _) ] => destruct b
      | [ |- (progress _) _ (match ?b with | _ => _ end) ] => destruct b
      end; try now constructor.
      destruct dir;
        (match goal with [ |- (progress _) _ (_ ?x') ] => apply progress_trans with (y := x') end; 
        [ constructor; [ reflexivity | constructor; simpl; lia ]
        | apply H ]).
    - delta MonotonousMatcher. cbn. intros.
      repeat match goal with
      | [ |- (progress _) _ (if ?b then _ else _) ] => destruct b
      | [ |- (progress _) _ (match ?b with | _ => _ end) ] => destruct b
      end; (apply IHr1 + apply IHr2); assumption.
    - intros. delta MonotonousMatcher. apply repeatMatcher_preserves_monotony.
      delta MonotonousMatcher. intros. apply IHr.
    - intros. cbn.
      repeat lazymatch goal with
      | [ |- (MonotonousMatcher _) (if ?b then _ else _) ] => destruct b
      end; delta MonotonousMatcher; cbn; intros;
        [ apply IHr1 | apply IHr2 ]; apply matcher_to_continuation; auto.
    (** With "meta-reduce" *)
    (*
    - intros. cbn beta delta iota.
      repeat lazymatch goal with
      | [ |- (MonotonousMatcher _) (let x := ?t1 in @?ft2 x) ] =>
        let xMeta := fresh x in
        remember t1 as xMeta;
        let full := eval cbn beta delta iota in (let x := xMeta in ft2 x) in
        let full' := eval cbn beta delta iota in (ft2 xMeta) in
        replace full with full' by (subst; reflexivity)
      | [ |- (MonotonousMatcher _) (if ?b then _ else _) ] => destruct b
      end.
      + cbv delta[MonotonousMatcher]. cbn. intros.
        subst. apply IHr1. apply matcher_to_continuation; auto.
      + cbv delta[MonotonousMatcher]. cbn. intros.
        subst. apply IHr2. apply matcher_to_continuation; auto. *)
    - delta MonotonousMatcher. cbn. intros.
      specialize (IHr rer dir). delta MonotonousMatcher in IHr. cbn in IHr.
      apply IHr. delta MonotonousContinuation. cbn. intros.
      repeat match goal with
      | [ |- (progress _) _ (if ?b then _ else _) ] => destruct b
      | [ |- (progress _) _ (match ?b with | _ => _ end) ] => destruct b
      end; try now constructor.
      delta MonotonousContinuation in H. admit.
    - admit.
    Admitted.
End Semantics.