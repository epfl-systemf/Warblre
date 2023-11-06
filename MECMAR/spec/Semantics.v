From Coq Require Import PeanoNat ZArith Bool Lia Program.Equality.
From Warblre Require Import Tactics Focus Result Base Patterns StaticSemantics Notation.

Import Result.Notations.
Import NoI.Coercions.
Local Open Scope result_flow.

(** 22.2.2 Pattern Semantics *)
Module Semantics.
  Import Patterns.
  Import Notation.

  (* Some coercions *)
  (* This one is used implicitly by the specification *)
  Coercion SomeCR: CaptureRange >-> CaptureRange_or_undefined.
  (* These are used to wrap things into the error monad we will be using *)
  Coercion wrap_CaptureRange(cr: CaptureRange) := @Success _ MatchError cr.
  Coercion state_to_result(x: MatchState) := @Success _ MatchError (Some x).

  (** 22.2.2.3.1 RepeatMatcher ( m, min, max, greedy, x, c, parenIndex, parenCount )
      The abstract operation RepeatMatcher takes arguments m (a Matcher), min (a non-negative integer), max (a non-
      negative integer or +∞), greedy (a Boolean), x (a MatchState), c (a MatcherContinuation), parenIndex (a non-negative 
      integer), and parenCount (a non-negative integer) and returns a MatchResult. It performs the following steps when 
      called:
    *)
  (* Coq wants to make sure the function will terminate; we do so by bounding recursion by an arbitrary fuel amount *)
  Fixpoint repeatMatcher' (m: Matcher) (min: non_neg_integer) (max: non_neg_integer_or_inf) (greedy: bool) (x: MatchState) (c: MatcherContinuation) (groupsWithin: IdSet.t) (fuel: nat): MatchResult :=
  match fuel with
  | 0 => out_of_fuel
  | S fuel' =>
    (* 1. If max = 0, return c(x). *)
    if (max =? 0)%NoI then c x else
    (* 2. Let d be a new MatcherContinuation with parameters (y) that captures m, min, max, greedy, x, c, parenIndex, and parenCount and performs the following steps when called: *)
    let d := fun (y: MatchState) =>
      (* a. Assert: y is a MatchState. *)
      (* b. If min = 0 and y's endIndex = x's endIndex, return failure. *)
      if (min =? 0)%nat && (MatchState.endIndex y =? MatchState.endIndex x)%Z
        then failure else
      (* c. If min = 0, let min2 be 0; otherwise let min2 be min - 1. *)
      let min2 :=
        if (min =? 0)%nat then 0
        else min - 1
      in
      (* d. If max = +∞, let max2 be +∞; otherwise let max2 be max - 1. *)
      let max2 :=
        if (max =? +∞)%NoI then +∞
        else (max - 1)%NoI
      in
      (* e. Return RepeatMatcher(m, min2, max2, greedy, y, c, parenIndex, parenCount). *)
      repeatMatcher' m min2 max2 greedy y c groupsWithin fuel'
    in
    (* 3. Let cap be a copy of x's captures List. *)
    let cap := MatchState.captures x in
    (* 4. For each integer k in the inclusive interval from parenIndex + 1 to parenIndex + parenCount, set cap[k] to undefined. *)
    set cap[groupsWithin ...] := undefined in
    (* 5. Let Input be x's input. *)
    let input := MatchState.input x in
    (* 6. Let e be x's endIndex. *)
    let e := MatchState.endIndex x in
    (* 7. Let xr be the MatchState (Input, e, cap). *)
    let xr := MatchState.make input e cap in
    (* 8. If min ≠ 0, return m(xr, d). *)
    if (min !=? 0)%nat
      then m xr d else
    (* 9. If greedy is false, then *)
    if greedy is false then
      (* a. Let z be c(x). *)
      let z := c x in
      (* b. If z is not failure, return z. *)
      if z is not failure
        then z else
      (* c. Return m(xr, d).*)
      m xr d
    else
    (* 10. Let z be m(xr, d). *)
    let z := m xr d in
    (* 11. If z is not failure, return z. *)
    if z is not failure
      then z else
    (* 12. Return c(x). *)
    c x
  end.

  Definition repeatMatcherFuel (min: non_neg_integer) (x: MatchState) := min + length (MatchState.input x) + 1.
  Definition repeatMatcher (m: Matcher) (min: non_neg_integer) (max: non_neg_integer_or_inf) (greedy: bool) (x: MatchState) (c: MatcherContinuation) (groupsWithin: IdSet.t): MatchResult :=
    repeatMatcher' m min max greedy x c groupsWithin (repeatMatcherFuel min x).

  Fixpoint compileSubPattern (self: Regex) (rer: RegExp) (direction: direction): Matcher := match self with
  | Char A invert =>  (** 22.2.2.7.1 CharacterSetMatcher ( rer, A, invert, direction ) *)
                      (* 1. Return a new Matcher with parameters (x, c) that captures rer, A, invert, and direction and performs the following steps when called: *)
                      fun (x: MatchState) (c: MatcherContinuation) =>
                        (* a. Assert: x is a MatchState. *)
                        (* b. Assert: c is a MatcherContinuation. *)
                        (* c. Let Input be x's input. *)
                        let input := MatchState.input x in
                        (* d. Let e be x's endIndex. *)
                        let e := MatchState.endIndex x in
                        (* e. If direction is forward, let f be e + 1. *)
                        (* f. Else, let f be e - 1. *)
                        let f := if direction is forward
                          then (e + 1)%Z
                          else (e - 1)%Z
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
                        let! chr =<< input[ index ] in
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
  | Disjunction r1 r2 => (** 22.2.2.3 Runtime Semantics: CompileSubpattern *)
                      (* 1. Let m1 be CompileSubpattern of Alternative with arguments rer and direction. *)
                      let m1 := compileSubPattern r1 rer direction in
                      (* 2. Let m2 be CompileSubpattern of Disjunction with arguments rer and direction. *)
                      let m2 := compileSubPattern r2 rer direction in
                      (* 3. Return a new Matcher with parameters (x, c) that captures m1 and m2 and performs the following steps when called: *)
                      fun (x: MatchState) (c: MatcherContinuation) =>
                        (* a. Assert: x is a MatchState. *)
                        (* b. Assert: x is a MatchState. *)
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
                        fun (s: MatchState) (c: MatcherContinuation) =>
                          (* i. Assert: x is a MatchState. *)
                          (* ii. Assert: c is a MatcherContinuation. *)
                          (* iii. Let d be a new MatcherContinuation with parameters (y) that captures c and m2 and performs the following steps when called: *)
                          let d := fun (s: MatchState) => 
                            (* 1. Assert: y is a MatchState. *)
                            (* 2. Return m2(y, c). *)
                            m2 s c
                          in
                          (* iv. Return m1(x, d). *)
                          m1 s d
                      (* 4. Else, *)
                      else
                        (* a. Assert: direction is backward. *)
                        (* b. Return a new Matcher with parameters (x, c) that captures m1 and m2 and performs the following steps when called: *)
                        fun (s: MatchState) (c: MatcherContinuation) =>
                          (* i. Assert: x is a MatchState. *)
                          (* ii. Assert: x is a MatchState. *)
                          (* iii. Let d be a new MatcherContinuation with parameters (y) that captures c and m1 and performs the following steps when called: *)
                          let d := fun (s: MatchState) =>
                            (* 1. Assert: y is a MatchState. *)
                            (* 2. Return m1(y, c). *)
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
                      fun (x: MatchState) (c: MatcherContinuation) =>
                        (* a. Assert: x is a MatchState. *)
                        (* b. Assert: c is a MatcherContinuation. *)
                        (* c. Let d be a new MatcherContinuation with parameters (y) that captures x, c, direction, and parenIndex and performs the following steps when called: *)
                        let d := fun (y: MatchState) =>
                          (* i. Assert: y is a MatchState. *)
                          (* ii. Let cap be a copy of y's captures List. *)
                          let cap := MatchState.captures y in
                          (* iii. Let Input be x's input. *)
                          let input := MatchState.input x in
                          (* iv. Let xe be x's endIndex. *)
                          let xe := MatchState.endIndex x in
                          (* v. Let ye be y's endIndex. *)
                          let ye := MatchState.endIndex y in
                          let! r =<<
                            (* vi. If direction is forward, then *)
                            if direction is forward then
                              (* 1. Assert: xe ≤ ye. *)
                              assert! (xe <=? ye)%Z ;
                              (* 2. Let r be the CaptureRange (xe, ye). *)
                              CaptureRange.make xe ye
                            (* vii. Else, *)
                            else
                              (* 1. Assert: direction is backward. *)
                              (* 2. Assert: ye ≤ xe. *)
                              assert! (ye <=? xe)%Z ;
                              (* 3. Let r be the CaptureRange (ye, xe). *)
                              CaptureRange.make ye xe
                          in
                          (* viii. Set cap[parenIndex + 1] to r. *)
                          set cap[id] := r in
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
                      fun (x: MatchState) (c: MatcherContinuation) =>
                        (* a. Assert: x is a MatchState. *)
                        (* b. Assert: c is a MatcherContinuation. *)
                        (* c. Let d be a new MatcherContinuation with parameters (y) that captures nothing and performs the following steps when called: *)
                        let d := fun (y: MatchState) =>
                          (* i. Assert: y is a MatchState. *)
                          (* ii. Return y. *)
                          y
                        in
                        (* d. Let r be m(x, d). *)
                        let r := m x d in
                        (* e. If r is failure, return failure. *)
                        if r is failure then
                          failure
                        else
                        (* f. Let y be r's MatchState. *)
                        destruct! Success (Some y) <- r in
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

  (** 22.2.2.2 Runtime Semantics: CompilePattern
      The syntax-directed operation CompilePattern takes argument rer (a RegExp Record) and returns an
      Abstract Closure that takes a List of characters and a non-negative integer and returns a MatchResult. It is
      defined piecewise over the following productions: *)
  Definition compilePattern (r: Regex) (rer: RegExp): list Character -> non_neg_integer -> MatchResult :=
    (* 1. Let m be CompileSubpattern of Disjunction with arguments rer and forward. *)
    let m := compileSubPattern r rer forward in
    (* 2. Return a new Abstract Closure with parameters (Input, index) that captures rer and m and performs the following steps when called: *)
    fun (input: list Character) (index: non_neg_integer) =>
      (* a. Assert: Input is a List of characters. *)
      (* b. Assert: 0 ≤ index ≤ the number of elements in Input. *)
      assert! (0 <=? index)%nat && (index <=? (length input))%nat ;
      (* c. Let c be a new MatcherContinuation with parameters (y) that captures nothing and performs the following steps when called: *)
      let c := fun (y: MatchState) =>
        (* i. Assert: y is a MatchState. *)
        (* ii. Return y. *)
        y
      in
      (* d. Let cap be a List of rer.[[CapturingGroupsCount]] undefined values, indexed 1 through rer.[[CapturingGroupsCount]]. *)
      let cap := DMap.empty CaptureRange_or_undefined in
      (* e. Let x be the MatchState (Input, index, cap). *)
      let x := match_state input (Z.of_nat index) cap in
      (* f. Return m(x, c). *)
      m x c.
End Semantics.