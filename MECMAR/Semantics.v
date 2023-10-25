(* From Coq Require Import Strings.String Structures.Orders Lia Program.Subset MSets FMaps. *)
From Coq Require Import PeanoNat ZArith Bool Lia Program.Equality.
From Warblre Require Import Tactics Focus Result Base Patterns StaticSemantics Notation.

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
      if (Nat.eqb min 0) && ((MatchState.endIndex y) =? (MatchState.endIndex x))%Z 
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
  
  Definition repeatMatcherFuel (min: non_neg_integer) (x: MatchState) := min + length (MatchState.input x) + 1.
  Definition repeatMatcher (m: Matcher) (min: non_neg_integer) (max: non_neg_integer_or_inf) (greedy: bool) (x: MatchState) (c: MatcherContinuation) (groupsWithin: IdSet.t): MatchResult :=
    repeatMatcher' m min max greedy x c groupsWithin (repeatMatcherFuel min x).

  Fixpoint compileSubPattern (self: Regex) (rer: RegExp) (direction: direction): Matcher := match self with
  | Char A invert =>  (** 22.2.2.7.1 CharacterSetMatcher ( rer, A, invert, direction ) *)
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
                          (if Direction.eqb direction forward
                          then e + 1
                          (* f. Else, let f be e - 1. *)
                          else e - 1)%Z
                        in
                        (* g. Let InputLength be the number of elements in Input. *)
                        let inputLength := Z.of_nat (length input) in
                        (* h. If f < 0 or f > InputLength, return failure. *)
                        if (f <? 0)%Z || (f >? inputLength)%Z then
                          failure
                        else
                          (* i. Let index be min(e, f). *)
                          let index := Z.min e f in
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
                              assert! (xe <=? ye)%Z ;
                              (* 2. Let r be the CaptureRange (xe, ye). *)
                              Success (CaptureRange.make xe ye)
                            (* vii. Else, *)
                            else
                              (* 1. Assert: direction is backward. *)
                              assert! direction is backward ;
                              (* 2. Assert: ye ≤ xe. *)
                              assert! (ye <=? xe)%Z ;
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

  (** 22.2.2.2 Runtime Semantics: CompilePattern *)
  (*  The syntax-directed operation CompilePattern takes argument rer (a RegExp Record) and returns an
      Abstract Closure that takes a List of characters and a non-negative integer and returns a MatchResult. It is
      defined piecewise over the following productions: *)
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
      let x := match_state input (Z.of_nat index) cap in
      (* f. Return m(x, c). *)
      m x c
    .

  (** Correctness proofs *)
  Create HintDb warblre.

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

  Ltac saturate_transitive rel trans := repeat match goal with
    | [ R1: rel ?S ?T, R2: rel ?T ?U |- _ ] => lazymatch goal with
      |  [ _ : rel S U |- _ ] => fail
      | [ |- _ ] => pose proof (trans S T U R1 R2)
      end
    end; try assumption.

  Ltac destruct_dps := repeat lazymatch goal with
  | [ H: directionalProgress ?d _ _ |- _ ] => is_constructor d; inversion H; clear H
  end.

  Lemma matchState_reconstruction: forall x, x = match_state (MatchState.input x) (MatchState.endIndex x) (MatchState.captures x).
  Proof. destruct x. reflexivity. Qed.

  Lemma progress_refl: forall dir x, (progress dir) x (Success x).
  Proof. intros. destruct dir; constructor; try reflexivity; constructor; normalize_Z_comp; apply Z.le_refl. Qed.
  #[export]
  Hint Resolve progress_refl: warblre.

  Lemma progress_trans: forall dir x y z, (progress dir) x (Success y) -> (progress dir) y z -> (progress dir) x z.
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

  Lemma progress_ignores_captures: forall dir x y cx cy,
        (progress dir) x (Success y) 
    ->  (progress dir) 
          (match_state (MatchState.input x) (MatchState.endIndex x) cx)
          (Success (match_state (MatchState.input y) (MatchState.endIndex y) cy)).
  Proof. intros. inversion H. constructor; simpl.
    - assumption.
    - destruct dir; destruct_dps; constructor; assumption.
  Qed.

  Ltac ignore_captures_change' x captures :=
    apply progress_trans with (y := (match_state (MatchState.input x) (MatchState.endIndex x) captures));
    [ replace x with (match_state (MatchState.input x) (MatchState.endIndex x) (MatchState.captures x)) at 1 by (destruct x; reflexivity);
      apply progress_ignores_captures; apply progress_refl
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

  Lemma matcher_to_continuation: forall dir str m c, MonotonousMatcher dir str m -> MonotonousContinuation dir str c 
    -> MonotonousContinuation dir str (fun (x: MatchState) => m x c).
  Proof. intros. unfold MonotonousContinuation. intros. apply H; assumption. Qed.

  Lemma repeatMatcher_preserves_monotony: forall fuel dir str x m min max greedy c groupsWithin,
            MonotonousMatcher dir str m
        ->  MonotonousContinuation dir str c
        ->  OnInput x str
        ->  progress dir x (repeatMatcher' m min max greedy x c groupsWithin fuel).
  Proof.
    induction fuel; intros; delta repeatMatcher'; try constructor.
    cbn.
    repeat match goal with
    | [ |- (progress _) _ (if ?b then _ else _) ] => destruct b
    end; solve
    [ apply H0; assumption
    | ignore_captures_change; apply H;
      [ assumption
      | delta MonotonousContinuation; cbn; intros;
        repeat match goal with
        | [ |- (progress _) _ (if ?b then _ else _) ] => destruct b
        end; try (now constructor);
        apply IHfuel with (str := str); assumption ] ].
  Qed.

  Lemma compileSubpattern_result_is_monotonous: forall r rer dir str, MonotonousMatcher dir str (compileSubPattern r rer dir).
  Proof.
    induction r.
    - delta MonotonousMatcher. cbn. intros.
      repeat match goal with
      | [ |- (progress _) _ (if ?b then _ else _) ] => destruct b
      | [ |- (progress _) _ (match ?b with | _ => _ end) ] => destruct b
      end; try now constructor.
      destruct dir;
        (lazymatch goal with [ |- progress _ _ (_ ?x') ] => apply progress_trans with (y := x') end;
        [ constructor; [ reflexivity | constructor; simpl; lia ]
        | apply H0; inversion H; subst; reflexivity ]).
    - delta MonotonousMatcher. cbn. intros.
      repeat match goal with
      | [ |- (progress _) _ (if ?b then _ else _) ] => destruct b
      | [ |- (progress _) _ (match ?b with | _ => _ end) ] => destruct b
      end; (apply IHr1 with (str := str) + apply IHr2 with (str := str)); assumption.
    - delta MonotonousMatcher. cbn. intros.
      apply repeatMatcher_preserves_monotony with (str := str); try assumption.
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

    Ltac mcbn_step t0 :=
      (*let _ := lazymatch goal with
      | [ |- context [ t0 ] ] => idtac
      | [ |- ?goal ] =>
        fail 100 "Goal" goal "should contain" t0
      end in  *)
      let t := (eval cbn beta iota in t0) in

      let prc from to By :=
        replace from with to by By
        (*let Tmp := fresh "Tmp" in
        assert (from = to) as Tmp by By:
        rewrite -> Tmp; 
        clear Tmp*)
      in

      let repl ft2 xMeta By :=
        let subs := eval cbn beta iota in (ft2 xMeta) in
        let _ := lazymatch goal with
        | [ |- context [ t0 ] ] =>
          prc t0 subs By
        | [ |- ?goal ] =>
          fail 100 "Goal" goal "was expected to contain" t0
        end in
        constr:(Some subs)
      in

      let remember_and_replace b pat :=
        let As := fresh in
        let Eq := fresh "Eq" in
        let _ := match goal with _ => 
          remember b as As eqn:Eq in |-;
          symmetry in Eq;
          destruct As in Eq;
          try discriminate
        end in
        lazymatch type of Eq with
        | _ = ?v =>
          repl pat v ltac:(rewrite -> Eq; reflexivity)
        | ?T => idtac T; fail 100 T
        end
      in

      lazymatch t with
      | let x := ?t1 in @?ft2 x => lazymatch goal with
        | [ _: ?xMeta = t1 |- _ ] => 
          is_var xMeta; 
          repl ft2 xMeta ltac:(subst; reflexivity)
        | [ |- _ ] =>
          let xMeta := fresh x in
          let _ := match goal with _ => remember t1 as xMeta in |- end in
          repl ft2 xMeta ltac:(subst; reflexivity)
        end

      | if ?b then _ else _ =>
        let app := (eval pattern b in t) in
        lazymatch app with
        | ?pat _ => lazymatch goal with
          | [ H: b = ?v |- _ ] =>
            repl pat v ltac:(rewrite -> H; reflexivity)
          | [ |- _ ] =>
            remember_and_replace b pat
          end
        end 

      | match ?b with | _ => _ end =>
        let app := (eval pattern b in t) in
        lazymatch app with
        | ?pat _ => lazymatch goal with
          | [ H: b = ?v |- _ ] =>
            repl pat v ltac:(rewrite -> H; reflexivity)
          | [ |- _ ] =>
            remember_and_replace b pat
          end
        end
      | _ => let T := type of t in constr:(@None T)
      end.

    Ltac mcbn_impl t :=
      let res := mcbn_step t in
      lazymatch res with
      | Some ?t' => mcbn_impl t'
      | None => try discriminate
      end.

    Tactic Notation "mcbn" constr(t) := mcbn_impl t.
    Tactic Notation "eql" "mcbn" hyp(H) := (revert H; pose proof I as H; match goal with | [ |- ?t = _ -> _ ] => mcbn t end; clear H; intros H).
    Tactic Notation "eqr" "mcbn" hyp(H) := (revert H; pose proof I as H; match goal with | [ |- _ = ?t -> _ ] => mcbn t end; clear H; intros H).



    Ltac boolean_simplifier := repeat match goal with
    | [ H: andb _ _ = true |- _ ] => pose proof (andb_prop _ _  H); clear H
    | [ H: orb _ _ = false |- _ ] => apply orb_false_elim in H; destruct H
    end.

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

    Ltac abstract_ite :=
      let f := focus_get_focus in
      let g := focus_get_goal in
      let f'' := (eval cbn in (focus_insert f § if [] then _ else _ §)) in
      let b := focus_excise f'' g in
      let Eq := fresh "Eq" in
      destruct b eqn:Eq in |-;
      match type of Eq with b = ?v =>
        (focus f'' replace with v by (rewrite -> Eq; reflexivity)); try discriminate
      end.

    Ltac make_let_meta :=
      let f := focus_get_focus in
      let g := focus_get_goal in
      let l := focus_excise f g in
      match l with
      | let x := ?b in @?t x =>
        let xMeta := fresh x in
        let Eq := fresh "Eq" in
        remember b as xMeta eqn:Eq in |-;
        let t' := constr:(t xMeta) in
        focus f replace with t' by (rewrite -> Eq; reflexivity)
      end.

    Ltac abstract_ite_impl f :=
      let g := focus_get_goal in
      let f'' := (eval cbn in (focus_insert f § if [] then _ else _ §)) in
      let b := focus_excise f'' g in
      let Eq := fresh "IfEq_" in
      destruct b eqn:Eq in |-;
      match type of Eq with b = ?v =>
        (focus f'' replace with v by (rewrite -> Eq; reflexivity)); try discriminate
      end.

    Ltac abstract_match_impl f :=
      let g := focus_get_goal in
      let l := focus_excise f g in
      match l with
      | match ?b with _ => _ end =>
        let Eq := fresh "MatchEq_" in
        destruct b eqn:Eq in |-;
        try discriminate
      end.

    Ltac make_let_meta_impl f :=
      let g := focus_get_goal in
      let l := focus_excise f g in
      match l with
      | let x := ?b in @?t x =>
        let xMeta := fresh x in
        let Eq := fresh "LetEq_" in
        remember b as xMeta eqn:Eq in |-;
        let t' := constr:(t xMeta) in
        focus f replace with t' by (rewrite -> Eq; reflexivity)
      end.
     

    Ltac meta_eval_impl f t :=
      assert_type f focus;
      match t with
      | if _ then _ else _ => abstract_ite_impl f
      | let _ := _ in _ => make_let_meta_impl f
      | match _ with _ => _ end => abstract_match_impl f
      | (fun _ => _) _ => idtac "funky"
      | ?l _ => meta_eval_impl constr:(focus_insert f (AppL Here)) l
      | _ => idtac
      end.
      
    Tactic Notation "focused" "meta-eval" := (
      let f := focus_get_focus in
      (
        let g := focus_get_goal in
        let t := focus_excise f g in
        meta_eval_impl f t)).

    Tactic Notation "reset" "(" ident(i) ":=" constr(t) ")" := clear i; set (i := t).

    Ltac check_not_duplicated H :=
      let T := type of H in
      lazymatch goal with
      | [ _: T, _: T |- _ ] => fail
      | [ |- _ ] => idtac
      end.
 
    Ltac saturate_progress_step dir := match goal with
    | [ H1: progress dir ?x (Success ?y), H2: progress ?dir ?y (Success ?z) |- _ ] =>
      let H := fresh "sp_trans_" H1 H2 in
      pose proof progress_trans as H;
      specialize H with (1 := H1) (2 := H2);
      check_not_duplicated H
    | [ H1: ?input = MatchState.input ?x,
        H2: ?endIndex = MatchState.endIndex ?x,
        H3: ?y = match_state ?input ?end_index ?c
      |- _ ] => let H := fresh "sp_change_" x y in
                pose proof (progress_refl dir x) as H;
                apply progress_ignores_captures with (cx := MatchState.captures x) (cy := c) in H;
                rewrite <- matchState_reconstruction in H;
                rewrite <- H1 in H;
                rewrite <- H2 in H;
                rewrite <- H3 in H;
                check_not_duplicated H
    end.
    Ltac saturate_progress dir := repeat saturate_progress_step dir.
    
    
    Notation "'validState' x" := (0 <= MatchState.endIndex x <= Z.of_nat (length (MatchState.input x)))%Z (at level 99).
    
    (*Ltac validate_state := match goal with
    | [ H: validState ?x |- validState ?x ] => exact H
    | [ H1: ?input = MatchState.input ?x,
        H2: ?endIndex = MatchState.endIndex ?x,
        H3: ?y = match_state ?input ?end_index ?c
      |- validState ?y ] => 
    *)

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

    Notation "x '[@' n ']'" := (match_state (MatchState.input x) n (MatchState.captures x)) (at level 50, left associativity).
    Notation "x '[$' c ']'" := (match_state (MatchState.input x) (MatchState.endIndex x) c) (at level 50, left associativity).
    Notation "x '[@' n '$' c ']'" := (match_state (MatchState.input x) n c) (at level 50, left associativity).

    Ltac auto_remember t := match t with
    | context[ _ [@ ?n ] ] => is_var n
    | context[ _ [@ ?n ] ] => let As := fresh "endIndex" in remember n as As
    (* | context[ compileSubPattern ?r ?rer ?dir ] => let As := fresh "m" in remember (compileSubPattern r rer dir) as As *)
    end.
    
    Tactic Notation "focused" "auto" "remember" := (
      let f := focus_get_focus in
      (
        let g := focus_get_goal in
        let t := focus_excise f g in
        idtac t;
        auto_remember t)).

    Lemma progress_ignores_captures': forall dir x iy ey cy,
          (progress dir) x (Success (match_state iy ey (MatchState.captures x)))
      ->  (progress dir) x (Success (match_state iy ey cy)).
    Proof. intros. inversion H. constructor; simpl.
      - assumption.
      - destruct dir; destruct_dps; constructor; assumption.
    Qed.
    
    Lemma progress_restate: forall dir x y,
          (progress dir) x (Success y)
      ->  (progress dir) x (Success (x [@ MatchState.endIndex y])).
    Proof. intros. inversion H. constructor; simpl in *.
      - reflexivity.
      - destruct dir; destruct_dps; constructor; assumption.
    Qed.

    Lemma matchState_id: forall x, x [@ MatchState.endIndex x ] = x.
    Proof. intros. destruct x; reflexivity. Qed.
    
    Lemma matchState_normalize: forall x e c, x [$ c] [@ e] = x [@ e] [$ c].
    Proof. intros. destruct x; reflexivity. Qed.
    
    Lemma progress_simplify_l: forall dir x y c, progress dir (x [$ c]) (Success y) <-> progress dir x (Success y).
    Proof. intros; split; intros; inversion H; constructor; simpl.
      - assumption.
      - destruct dir; destruct_dps; constructor; assumption.
      - assumption.
      - destruct dir; destruct_dps; constructor; assumption.
    Qed.
    
    Lemma progress_simplify_r: forall dir x y c, progress dir x (Success (y [$ c])) <-> progress dir x (Success y).
    Proof. intros; split; intros; inversion H; constructor; simpl.
      - assumption.
      - destruct dir; destruct_dps; constructor; assumption.
      - assumption.
      - destruct dir; destruct_dps; constructor; assumption.
    Qed.
    
    Lemma progress_ignores_captures_r: forall dir x n c,
          (progress dir) x (Success (x [@ n $ c]))
      <->  (progress dir) x (Success (x [@ n])).
    Proof. intros; split; intros; inversion H; constructor; simpl.
      - assumption.
      - destruct dir; destruct_dps; constructor; assumption.
      - reflexivity.
      - destruct dir; destruct_dps; constructor; assumption.
    Qed.
    
    Lemma progress_normalize: forall dir x y, progress dir x (Success y) -> y = (x [@ MatchState.endIndex y] [$ MatchState.captures y]).
    Proof. intros. inversion H. destruct y. cbn in *. subst. reflexivity. Qed.

    Ltac clean_progress := repeat
    (   rewrite -> matchState_id in *
    ||  rewrite -> matchState_normalize in *
    ||  rewrite -> progress_ignores_captures_r in *
    ||  rewrite -> progress_simplify_l in *
    ||  rewrite -> progress_simplify_r in *
    ||  lazymatch goal with
        | [ H: progress _ ?x (Success (?x [@ _ ] [$ _ ])) |- _ ] => fail
        | [ H: progress _ ?x (Success ?y) |- _ ] =>
          let Eq := fresh "Eq" x y in
          pose proof progress_normalize _ _ _ H as Eq;
          rewrite -> Eq in *
        end
    ||  assumption).
    
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
        let H := fresh a "'" in
        pose proof a as H;
        specialize H with (1 := b)
      end
    end.

    Ltac specialize_once := match goal with
    | [ H: _, H': _ |- _ ] => specialize H with (1 := H')
    end.

    Ltac search_intermediate_value := try assumption; match goal with
      | [ H: ?c ?y = Success ?z |- exists x, _ /\ ?c x = Success ?z ] => exists y; split; [ try assumption | apply H ]
      end; match goal with
      | [ |- progress ?dir _ _ ] => saturate_progress dir; try assumption
      end.

    Lemma repeatMatcher_intermediate_value: forall fuel dir x m min max greedy c groupsWithin z,
          (repeatMatcher' m min max greedy x c groupsWithin fuel) = Success z
      ->  (forall x' c' z', m x' c' = Success z' -> exists y', progress dir x' (Success y') /\ c' y' = Success z')
      ->  exists y, progress dir x (Success y) /\ c y = Success z.
    Proof.
      induction fuel; deltaf repeatMatcher'; cbn; intros;
        focus § _ [] _ § auto destruct in H.
      - discriminate.
      - search_intermediate_value. apply progress_refl.
      - auto_specialize; Coq.Program.Tactics.destruct_conjs.
        focus § _ [] _ § auto destruct in H3.
        auto_specialize; Coq.Program.Tactics.destruct_conjs.
        search_intermediate_value. clean_progress.
      - search_intermediate_value. apply progress_refl.
      - auto_specialize; Coq.Program.Tactics.destruct_conjs.
        focus § _ [] _ § auto destruct in H3.
        auto_specialize; Coq.Program.Tactics.destruct_conjs.
        search_intermediate_value. clean_progress.
      - auto_specialize; Coq.Program.Tactics.destruct_conjs.
        focus § _ [] _ § auto destruct in H3.
        auto_specialize; Coq.Program.Tactics.destruct_conjs.
        search_intermediate_value. clean_progress.
      - search_intermediate_value. apply progress_refl.
    Qed.

    Lemma compiledSubPattern_intermediate_value: forall r rer dir x c z, (compileSubPattern r rer dir) x c = Success z 
      -> exists y, progress dir x (Success y) /\ c y = Success z.
    Proof.
      induction r; intros rer dir x c z; cbn;
      focus § _ [] _ -> _ § auto destruct; intros.
      + search_intermediate_value. step_progress.
      + repeat (specialize_once; Coq.Program.Tactics.destruct_conjs). search_intermediate_value.
      + repeat (specialize_once; Coq.Program.Tactics.destruct_conjs). search_intermediate_value.
      + apply repeatMatcher_intermediate_value with (1 := H). intros.
        repeat (specialize_once; Coq.Program.Tactics.destruct_conjs). search_intermediate_value.
      + repeat (specialize_once; Coq.Program.Tactics.destruct_conjs). search_intermediate_value.
      + repeat (specialize_once; Coq.Program.Tactics.destruct_conjs). search_intermediate_value.
      + specialize IHr with (1 := H). Coq.Program.Tactics.destruct_conjs.
        focus §_ [] _§ auto destruct in H1. search_intermediate_value. clean_progress.
      + search_intermediate_value. clean_progress. auto with warblre.
      Qed.

    Lemma compiledSubPattern_never_triggers_assertions: forall r rer dir x c,
          validState x
      ->  (forall x', validState x' -> progress dir x (Success x') -> c x' <> assertion_failed)
      ->  (compileSubPattern r rer dir) x c <> assertion_failed.
    Proof.
      induction r; intros.
      - deltaf compileSubPattern. cbn beta delta iota.
        lazymatch goal with | [ |- ?t <> _ ] => mcbn t end; try easy.
        + apply H0. 
          * subst. destruct dir; cbn in *; hypotheses_reflector; lia.
          * subst. destruct dir; (constructor; try solve [ reflexivity | constructor; cbn; lia ]).
        + destruct (input [index]) eqn:Eq3; try easy.
          intros Falso. injection Eq0; clear Eq0. injection Falso; clear Falso. intros. subst f0. subst f1.
          rewrite -> Indexing.indexing_Failure in Eq3.
          hypotheses_reflector;
          normalize_Z_comp;
          spec_reflector Z.ltb_spec0;
          destruct dir eqn:Eq_dir;
          simpl in *.
          all: subst; ztac; lia.
      - deltaf compileSubPattern. cbn beta delta iota.
        repeat progress lazymatch goal with | [ |- ?t _ _ <> _ ] => mcbn t end; try easy.
        repeat progress lazymatch goal with | [ |- ?t <> _ ] => mcbn t end; try easy.
        + subst r. subst m1. apply IHr1; assumption.
        + subst m2. apply IHr2; assumption.
      - deltaf compileSubPattern. cbn beta delta iota.
        repeat progress lazymatch goal with | [ |- ?t _ _ <> _ ] => mcbn t end; try easy.
        admit.
      - delta compileSubPattern. cbn beta delta iota.
        repeat progress lazymatch goal with | [ |- ?t _ _ <> _ ] => mcbn t end; try easy;
        repeat progress lazymatch goal with | [ |- ?t <> _ ] => mcbn t end; try easy.
        + subst m1. apply IHr1; try assumption. subst d. subst m2. intros. apply IHr2; try assumption. intros. apply H0; try assumption. apply progress_trans with (y := x'); assumption.
        + subst m2. apply IHr2; try assumption. subst d. subst m1. intros. apply IHr1; try assumption. intros. apply H0; try assumption. apply progress_trans with (y := x'); assumption.
      - deltaf compileSubPattern. cbn beta delta iota.
        repeat lazymatch goal with | [ |- ?t _ _ <> _ ] => mcbn t end; try easy.
        repeat lazymatch goal with | [ |- ?t <> _ ] => mcbn t end; try easy.
        subst m. apply IHr; try assumption. intros.
        subst d.
        repeat lazymatch goal with | [ |- ?t <> _ ] => mcbn t end; try easy.
        + apply H0.
          * admit.
          * subst. apply progress_trans with (y := x'); try assumption. dependent destruction H2. rewrite -> H2. ignore_captures_change.
            apply progress_refl.
        + destruct dir.
          * 
            dependent destruction H2. dependent destruction H3. subst.
            spec_denoter Z.leb_spec0. rewrite -> H3 in Eq. easy.
          * dependent destruction H2. dependent destruction H3. subst.
            normalize_Z_comp.
            spec_denoter Z.leb_spec0. rewrite -> H3 in Eq. easy.
      - deltaf compileSubPattern. cbn beta delta iota.
        repeat progress lazymatch goal with | [ |- ?t _ _ <> _ ] => mcbn t end; try easy;
        repeat progress lazymatch goal with | [ |- ?t <> _ ] => mcbn t end; try easy.
        + apply H0. 
          * admit.
          * subst. ignore_captures_change. apply progress_refl.
        + rewrite <- Eq0. subst m. apply IHr.
          intros. subst d. easy.
    Admitted.

    Theorem compiledPattern_never_triggers_internal_assertions: forall r rer input i, 0 <= i <= (length input) -> compilePattern r rer input i <> assertion_failed.
    Proof.
      intros. delta compilePattern. cbn beta.
      repeat lazymatch goal with | [ |- ?t _ _ <> _ ] => mcbn t end; try easy;
      repeat lazymatch goal with | [ |- ?t <> _ ] => mcbn t end; try easy.
      - subst m. apply compiledSubPattern_never_triggers_assertions. 
        * subst x. cbn. hypotheses_reflector. spec_reflector Nat.leb_spec0. lia.
        * intros. subst c. easy.
      - hypotheses_reflector; spec_reflector Nat.leb_spec0; lia.
    Qed.
    
End Semantics.