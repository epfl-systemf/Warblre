(* From Coq Require Import Strings.String Structures.Orders Lia Program.Subset MSets FMaps. *)
From Coq Require Import PeanoNat ZArith Bool Lia.
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
  Definition repeatMatcher (m: Matcher) (min: non_neg_integer) (max: non_neg_integer_or_inf) (greedy: bool) (x: MatchState) (c: MatcherContinuation) (groupsWithin: IdSet.t): MatchResult :=
    repeatMatcher' m min max greedy x c groupsWithin (min + length (MatchState.input x) + 1).

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

  Tactic Notation "delta" reference(id) := cbv delta [ id ].
  Tactic Notation "delta" reference(id) "in" hyp(h) := cbv delta [ id ] in h.

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

  Ltac normalize_Z_comp := repeat
  (   rewrite -> Z.ge_le_iff in *
  ).
  
  About Z.le_refl.
  Lemma progress_refl: forall dir x, (progress dir) x (Success x).
  Proof. intros. destruct dir; constructor; try reflexivity; constructor; normalize_Z_comp; apply Z.le_refl. Qed.

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

  (** Sounds good, doesn't work *)
  (*
  Ltac remember_goal_part pat x As := idtac pat; match goal with
  | [ |- pat ] => idtac x; remember x as A
  end.
  Tactic Notation "tmp" ident(x) "of" uconstr(pat) "as" simple_intropattern(As) := remember_goal_part pat x As. *)

  (** Meta-call-by-name: like call by name, but bound computation are promoted to hypotheses. E.g. from
      let x := <expr1> in <expr2>
      to
      [x |-> x']<expr2>
      where x' is a fresh meta-variable and with
      x = <expr1>
      added as an hypothesis

      This was not yet useful, but might be once we move to more involved properties.
   *)
  Ltac mcbn_proto := repeat
  (   cbn beta delta iota
  ||  lazymatch goal with
      (* Annoying context *)
      | [ |- (MonotonousMatcher _) (let x := ?t1 in @?ft2 x) ] =>
        let xMeta := fresh x in
        remember t1 as xMeta;
        let full := eval cbn beta delta iota in (let x := xMeta in ft2 x) in
        let full' := eval cbn beta delta iota in (ft2 xMeta) in
        replace full with full' by (subst; reflexivity)
      (* The same for if-then-else/match ?*)
      end).

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
End Semantics.