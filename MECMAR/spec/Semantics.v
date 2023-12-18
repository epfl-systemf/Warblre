From Coq Require Import PeanoNat ZArith Bool Lia Program.Equality List.
From Warblre Require Import Tactics Focus Result Base Patterns StaticSemantics Notation List.

Import Result.Notations.
Import NoI.Coercions.
Local Open Scope result_flow.

(** 22.2.2 Pattern Semantics *)
Module Semantics.
  Import Patterns.
  Import Notation.

  (* Some coercions *)
  (* These ones is used implicitly by the specification *)
  Coercion CaptureRange_or_undefined(cr: CaptureRange) := (Some cr).
  Coercion MatchState_or_failure(x: MatchState) := (Some x).
  Coercion Z.of_nat: nat >-> Z.
  (* These are used to wrap things into the error monad we will be using *)
  Coercion wrap_option := fun (T: Type) (t: option T) => @Success (option T) MatchError t.
  Coercion wrap_bool := fun (t: bool) => @Success bool MatchError t.

  Coercion wrap_Matcher := fun (m: Matcher) => @Success Matcher CompileError m.
  Coercion wrap_CharSet := fun (s: CharSet) => @Success CharSet CompileError s.
  Create HintDb Warblre_coercions.
  #[export]
  Hint Unfold CaptureRange_or_undefined MatchState_or_failure wrap_option wrap_bool : Warblre_coercions.

  (** 22.2.2.3.1 RepeatMatcher ( m, min, max, greedy, x, c, parenIndex, parenCount )
      The abstract operation RepeatMatcher takes arguments m (a Matcher), min (a non-negative integer), max (a non-
      negative integer or +∞), greedy (a Boolean), x (a MatchState), c (a MatcherContinuation), parenIndex (a non-negative 
      integer), and parenCount (a non-negative integer) and returns a MatchResult. It performs the following steps when 
      called:
    *)
  (* Coq wants to make sure the function will terminate; we do so by bounding recursion by an arbitrary fuel amount *)
  Fixpoint repeatMatcher' (m: Matcher) (min: non_neg_integer) (max: non_neg_integer_or_inf) (greedy: bool) (x: MatchState) (c: MatcherContinuation) (parenIndex parenCount: non_neg_integer) (fuel: nat): MatchResult :=
  match fuel with
  | 0 => out_of_fuel
  | S fuel' =>
    (* 1. If max = 0, return c(x). *)
    if (max =? 0)%NoI then c x else
    (* 2. Let d be a new MatcherContinuation with parameters (y) that captures m, min, max, greedy, x, c, parenIndex, and parenCount and performs the following steps when called: *)
    let d: MatcherContinuation := fun (y: MatchState) =>
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
      repeatMatcher' m min2 max2 greedy y c parenIndex parenCount fuel'
    in
    (* 3. Let cap be a copy of x's captures List. *)
    let cap := MatchState.captures x in
    (* 4. For each integer k in the inclusive interval from parenIndex + 1 to parenIndex + parenCount, set cap[k] to undefined. *)
    set cap[(parenIndex + 1) --- (parenIndex + parenCount + 1) ] := undefined in
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
      let! z =<< c x in
      (* b. If z is not failure, return z. *)
      if z is not failure
        then z else
      (* c. Return m(xr, d).*)
      m xr d
    else
    (* 10. Let z be m(xr, d). *)
    let! z =<< m xr d in
    (* 11. If z is not failure, return z. *)
    if z is not failure
      then z else
    (* 12. Return c(x). *)
    c x
  end.

  Definition repeatMatcherFuel (min: non_neg_integer) (x: MatchState) := min + length (MatchState.input x) + 1.
  Definition repeatMatcher (m: Matcher) (min: non_neg_integer) (max: non_neg_integer_or_inf) (greedy: bool) (x: MatchState) (c: MatcherContinuation) (parenIndex parenCount: non_neg_integer): MatchResult :=
    repeatMatcher' m min max greedy x c parenIndex parenCount (repeatMatcherFuel min x).

  (** 22.2.2.6 Runtime Semantics: CompileQuantifierPrefix *)
  Module CompiledQuantifierPrefix.
    Record type := make {
      min: non_neg_integer;
      max: non_neg_integer_or_inf;
    }.

    Module Notations.
      Notation CompiledQuantifierPrefix := type.
      Notation compiled_quantifier_prefix := make.
    End Notations.
  End CompiledQuantifierPrefix.
  Import CompiledQuantifierPrefix.Notations.

  Definition compileQuantifierPrefix (self: QuantifierPrefix): CompiledQuantifierPrefix := match self with
  | Star => compiled_quantifier_prefix 0 +∞
  | Plus => compiled_quantifier_prefix 1 +∞
  | Question => compiled_quantifier_prefix 0 1
  | RepExact i => compiled_quantifier_prefix i i
  | RepPartialRange i => compiled_quantifier_prefix i +∞
  | RepRange i j _ => compiled_quantifier_prefix i j
  end.

  (** 22.2.2.5 Runtime Semantics: CompileQuantifier *)
  Module CompiledQuantifier.
    Record type := make {
      min: non_neg_integer;
      max: non_neg_integer_or_inf;
      greedy: bool;
    }.

    Module Notations.
      Notation CompiledQuantifier := type.
      Notation compiled_quantifier := make.
    End Notations.
  End CompiledQuantifier.
  Import CompiledQuantifier.Notations.

  Definition compileQuantifier(self: Quantifier): CompiledQuantifier := match self with
  | Greedy q => (* Quantifier :: QuantifierPrefix *)
      (* 1. Let qp be CompileQuantifierPrefix of QuantifierPrefix. *)
      let qp := compileQuantifierPrefix q in
      (* 2. Return the Record { [[Min]]: qp.[[Min]], [[Max]]: qp.[[Max]], [[Greedy]]: true }. *)
      compiled_quantifier (CompiledQuantifierPrefix.min qp) (CompiledQuantifierPrefix.max qp) true
  | Lazy q => (* Quantifier :: QuantifierPrefix ? *)
      (* 1. Let qp be CompileQuantifierPrefix of QuantifierPrefix. *)
      let qp := compileQuantifierPrefix q in
      (* 2. Return the Record { [[Min]]: qp.[[Min]], [[Max]]: qp.[[Max]], [[Greedy]]: false }. *)
      compiled_quantifier (CompiledQuantifierPrefix.min qp) (CompiledQuantifierPrefix.max qp) false
  end.

  (** 22.2.2.7.1 CharacterSetMatcher ( rer, A, invert, direction ) *)
  Definition characterSetMatcher (rer: RegExp) (A: CharSet) (invert: bool) (direction: direction): Matcher :=
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
      let! found =<< CharSet.exist A (fun a => Character.eqb a cc) in
      (* m. If invert is false and found is false, return failure. *)
      if (invert is false) && (found is false) then
        failure
      (* n. If invert is true and found is true, return failure. *)
      else if (invert is true) && (found is true) then
        failure
      else
      (* o. Let cap be x's captures List. *)
      let cap := MatchState.captures x in
      (* p. Let y be the MatchState (Input, f, cap). *)
      let y := match_state input f cap in
      (* q. Return c(y). *)
      c y.

  (** 22.2.2.7.2 BackreferenceMatcher ( rer, n, direction ) *)
  Definition backreferenceMatcher (rer: RegExp) (n: positive_integer) (direction: direction): Matcher :=
    (* 1. Assert: n ≥ 1. *)
    (* 2. Return a new Matcher with parameters (x, c) that captures rer, n, and direction and performs the following steps when called: *)
    fun (x: MatchState) (c: MatcherContinuation) =>
      (* a. Assert: x is a MatchState. *)
      (* b. Assert: c is a MatcherContinuation. *)
      (* c. Let Input be x's input. *)
      let input := MatchState.input x in
      (* d. Let cap be x's captures List. *)
      let cap := MatchState.captures x in
      (* e. Let r be cap[ n ]. *)
      let! r =<< cap[n] in
      (* f. If r is undefined, return c(x). *)
      if r is undefined
        then c x else
      destruct! Some r <- r in
      (* g. Let e be x's endIndex. *)
      let e := MatchState.endIndex x in
      (* h. Let rs be r's startIndex. *)
      let rs := CaptureRange.startIndex r in
      (* i. Let re be r's endIndex. *)
      let re := CaptureRange.endIndex r in
      (* j. Let len be re - rs. *)
      let len := (re - rs)%Z in
      (* k. If direction is forward, let f be e + len. *)
      let f := if direction is forward
        then (e + len)%Z
      (* l. Else, let f be e - len. *)
        else (e - len)%Z
      in
      (* m. Let InputLength be the number of elements in Input. *)
      let inputLength := length input in
      (* n. If f < 0 or f > InputLength, return failure. *)
      if (f <? 0)%Z || (f >? inputLength)%Z
        then failure else
      (* o. Let g be min(e, f). *)
      let g := Z.min e f in
      (* p. If there exists an integer i in the interval from 0 (inclusive) to len (exclusive) such that Canonicalize(rer, Input[rs + i]) is not Canonicalize(rer, Input[g + i]), return failure. *)
      let! b: bool =<< List.Exists.exist (List.Range.Int.Bounds.range 0 len) (fun (i: Z) =>
        let! rsi: Character =<< input[ (rs + i)%Z ] in
        let! gi: Character =<< input[ (g + i)%Z ] in
        (rsi !=? gi)%Chr)
      in
      if b
        then failure else
      (* q. Let y be the MatchState (Input, f, cap). *)
      let y := match_state input f cap in
      (* r. Return c(y). *)
      c y.

  (** 22.2.2.9 Runtime Semantics: CompileToCharSet *)

  (** 22.2.2.9.1 CharacterRange *)

  Definition characterRange (a b: CharSet): Result CharSet CompileError :=
    (* 1. Assert: A and B each contain exactly one character. *)
    assert! (CharSet.size a =? 1)%nat && (CharSet.size b =? 1)%nat ;
    (* 2. Let a be the one character in CharSet A. *)
    let! a =<< CharSet.unique a in
    (* 3. Let b be the one character in CharSet B. *)
    let! b =<< CharSet.unique b in
    (* 4. Let i be the character value of character a. *)
    let i := Character.numeric_value a in
    (* 5. Let j be the character value of character b. *)
    let j := Character.numeric_value b in
    (* 6. Assert: i ≤ j. *)
    assert! (i <=? j)%nat ;
    (* 7. Return the CharSet containing all characters with a character value in the inclusive interval from i to j. *)
    CharSet.range i j.

  Definition compileToCharSet_ClassAtom (self: ClassAtom) (rer: RegExp): Result CharSet CompileError  := match self with
  | SourceCharacter chr =>
      CharSet.singleton chr
  end.

  Fixpoint compileToCharSet (self: ClassRanges) (rer: RegExp): Result CharSet CompileError := match self with
  | EmptyCR =>
      (* 1. Return the empty CharSet. *)
      CharSet.empty
  | ClassAtomCR ca cr =>
      (* 1. Let A be CompileToCharSet of ClassAtom with argument rer. *)
      let! A =<< compileToCharSet_ClassAtom ca rer in
      (* 2. Let B be CompileToCharSet of NonemptyClassRangesNoDash with argument rer. *)
      let! B =<< compileToCharSet cr rer in
      (* 3. Return the union of CharSets A and B. *)
      CharSet.union A B
  | RangeCR l h t =>
      (* 1. Let A be CompileToCharSet of the first ClassAtom with argument rer. *)
      let! A =<< compileToCharSet_ClassAtom l rer in
      (* 2. Let B be CompileToCharSet of the second ClassAtom with argument rer. *)
      let! B =<< compileToCharSet_ClassAtom h rer in
      (* 3. Let C be CompileToCharSet of ClassRanges with argument rer. *)
      let! C =<< compileToCharSet t rer in
      (* 4. Let D be CharacterRange(A, B). *)
      let! D =<< characterRange A B in
      (* 5. Return the union of D and C. *)
      CharSet.union D C
  end.


  (** 22.2.2.8 Runtime Semantics: CompileCharacterClass *)

  Module CompiledCharacterClass.
    Record type := make {
      charSet: CharSet;
      invert: bool;
    }.
  End CompiledCharacterClass.
  Notation compiled_character_class := CompiledCharacterClass.make.
  Notation CompiledCharacterClass := CompiledCharacterClass.type.

  Definition compileCharacterClass (self: CharClass) (rer: RegExp): Result CompiledCharacterClass CompileError := match self with
  | NoninvertedCC crs =>
      let! a =<< compileToCharSet crs rer in
      Success (compiled_character_class a false)
  | InvertedCC crs =>
      let! a =<< compileToCharSet crs rer in
      Success (compiled_character_class a true)
  end.

  Fixpoint compileSubPattern (self: Regex) (ctx: RegexContext) (rer: RegExp) (direction: direction): Result Matcher CompileError := match self with
  | Empty =>          (* Alternative :: [empty] *)
                      (* 1. Return a new Matcher with parameters (x, c) that captures nothing and performs the following steps when called: *)
                      (fun (x: MatchState) (c: MatcherContinuation) =>
                        (* a. Assert: x is a MatchState. *)
                        (* b. Assert: c is a MatcherContinuation. *)
                        (* c. Return c(x). *)
                        c x): Matcher
  | Char c =>
      (* 1. Let ch be the character matched by PatternCharacter. *)
      let ch := c in
      (* 2. Let A be a one-element CharSet containing the character ch. *)
      let A := CharSet.singleton c in
      (* 3. Return CharacterSetMatcher(rer, A, false, direction). *)
      characterSetMatcher rer A false direction
  | Dot =>
      (* 1. Let A be the CharSet of all characters. *)
      let A := CharSet.all in
      (* 2. If rer.[[DotAll]] is not true, then *)
      let A := if RegExp.dotAll rer is not true
        (* a. Remove from A all characters corresponding to a code point on the right-hand side of the LineTerminator production. *)
        then CharSet.remove_all A CharSet.line_terminators
        else A
      in
      (* 3. Return CharacterSetMatcher(rer, A, false, direction). *)
      characterSetMatcher rer A false direction
  | CharacterClass cc =>
      (* 1. Let cc be CompileCharacterClass of CharacterClass with argument rer. *)
      let! cc =<< compileCharacterClass cc rer in
      (* 2. Return CharacterSetMatcher(rer, cc.[[CharSet]], cc.[[Invert]], direction). *)
      characterSetMatcher rer (CompiledCharacterClass.charSet cc) (CompiledCharacterClass.invert cc) direction
  | Disjunction r1 r2 => (** 22.2.2.3 Runtime Semantics: CompileSubpattern *)
                      (* 1. Let m1 be CompileSubpattern of Alternative with arguments rer and direction. *)
                      let! m1 =<< compileSubPattern r1 (Disjunction_left r2 :: ctx) rer direction in
                      (* 2. Let m2 be CompileSubpattern of Disjunction with arguments rer and direction. *)
                      let! m2 =<< compileSubPattern r2 (Disjunction_right r1 :: ctx) rer direction in
                      (* 3. Return a new Matcher with parameters (x, c) that captures m1 and m2 and performs the following steps when called: *)
                      (fun (x: MatchState) (c: MatcherContinuation) =>
                        (* a. Assert: x is a MatchState. *)
                        (* b. Assert: x is a MatchState. *)
                        (* c. Let r be m1(x, c). *)
                        let! r =<< m1 x c in
                        (* d. If r is not failure, return r. *)
                        if r is not failure then
                          r
                        else
                        (* e. Return m2(x, c). *)
                        m2 x c): Matcher
  | Quantified r qu => (** Term :: Atom Quantifier *)
                      (* 1. Let m be CompileAtom of Atom with arguments rer and direction. *)
                      let! m =<< compileSubPattern r  (Quantified_inner qu :: ctx) rer direction in
                      (* 2. Let q be CompileQuantifier of Quantifier. *)
                      let q := compileQuantifier qu in
                      (* 3. Assert: q.[[Min]] ≤ q.[[Max]]. *)
                      (* Holds by construction *)
                      (* 4. Let parenIndex be CountLeftCapturingParensBefore(Term). *)
                      let parenIndex := countLeftCapturingParensBefore r ctx in
                      (* 5. Let parenCount be CountLeftCapturingParensWithin(Atom). *)
                      let parenCount := countLeftCapturingParensWithin r (Quantified_inner qu :: ctx) in
                      (* 6. Return a new Matcher with parameters (x, c) that captures m, q, parenIndex, and parenCount and performs the following steps when called: *)
                      (fun (x: MatchState) (c: MatcherContinuation) =>
                        (* a. Assert: x is a MatchState. *)
                        (* b. Assert: c is a MatcherContinuation. *)
                        (* c. Return RepeatMatcher(m, q.[[Min]], q.[[Max]], q.[[Greedy]], x, c, parenIndex, parenCount). *)
                        repeatMatcher m (CompiledQuantifier.min q) (CompiledQuantifier.max q) (CompiledQuantifier.greedy q) x c parenIndex parenCount): Matcher
  | Seq r1 r2     =>  (**  Alternative :: Alternative Term *)
                      (* 1. Let m1 be CompileSubpattern of Alternative with arguments rer and direction. *)
                      let! m1 =<< compileSubPattern r1 (Seq_left r2 :: ctx) rer direction in
                      (* 2. Let m2 be CompileSubpattern of Term with arguments rer and direction. *)
                      let! m2 =<< compileSubPattern r2 (Seq_right r1 :: ctx) rer direction in
                      (* 3. If direction is forward, then *)
                      if direction is forward then
                        (* a. Return a new Matcher with parameters (x, c) that captures m1 and m2 and performs the following steps when called: *)
                        (fun (s: MatchState) (c: MatcherContinuation) =>
                          (* i. Assert: x is a MatchState. *)
                          (* ii. Assert: c is a MatcherContinuation. *)
                          (* iii. Let d be a new MatcherContinuation with parameters (y) that captures c and m2 and performs the following steps when called: *)
                          let d: MatcherContinuation := fun (s: MatchState) => 
                            (* 1. Assert: y is a MatchState. *)
                            (* 2. Return m2(y, c). *)
                            m2 s c
                          in
                          (* iv. Return m1(x, d). *)
                          m1 s d): Matcher
                      (* 4. Else, *)
                      else
                        (* a. Assert: direction is backward. *)
                        (* b. Return a new Matcher with parameters (x, c) that captures m1 and m2 and performs the following steps when called: *)
                        (fun (s: MatchState) (c: MatcherContinuation) =>
                          (* i. Assert: x is a MatchState. *)
                          (* ii. Assert: x is a MatchState. *)
                          (* iii. Let d be a new MatcherContinuation with parameters (y) that captures c and m1 and performs the following steps when called: *)
                          let d: MatcherContinuation := fun (s: MatchState) =>
                            (* 1. Assert: y is a MatchState. *)
                            (* 2. Return m1(y, c). *)
                            m1 s c 
                          in
                          (* iv. Return m2(x, d). *)
                          m2 s d): Matcher
  | Group id r    =>  (**  Atom :: ( GroupSpecifier_opt Disjunction ) *)
                      (* 1.  *)
                      let! m =<< compileSubPattern r (Group_inner id :: ctx) rer direction in
                      (* 2. Let parenIndex be CountLeftCapturingParensBefore(Atom). *)
                      let parenIndex := countLeftCapturingParensBefore self ctx in
                      (* 3. Return a new Matcher with parameters (x, c) that captures direction, m, and parenIndex and performs the following steps when called: *)
                      (fun (x: MatchState) (c: MatcherContinuation) =>
                        (* a. Assert: x is a MatchState. *)
                        (* b. Assert: c is a MatcherContinuation. *)
                        (* c. Let d be a new MatcherContinuation with parameters (y) that captures x, c, direction, and parenIndex and performs the following steps when called: *)
                        let d: MatcherContinuation := fun (y: MatchState) =>
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
                          set cap[parenIndex + 1] := r in
                          (* ix. Let z be the MatchState (Input, ye, cap). *)
                          let z := match_state input ye cap in
                          (* x. Return c(z). *)
                          c z
                        in
                        (* d. Return m(x, d). *)
                        m x d): Matcher
  | Lookahead r    => (**  Assertion :: (?= Disjunction ) *)
                      (* 1. Let m be CompileSubpattern of Disjunction with arguments rer and forward. *)
                      let! m =<< compileSubPattern r (Lookahead_inner :: ctx) rer forward in
                      (* 2. Return a new Matcher with parameters (x, c) that captures m and performs the following steps when called: *)
                      (fun (x: MatchState) (c: MatcherContinuation) =>
                        (* a. Assert: x is a MatchState. *)
                        (* b. Assert: c is a MatcherContinuation. *)
                        (* c. Let d be a new MatcherContinuation with parameters (y) that captures nothing and performs the following steps when called: *)
                        let d: MatcherContinuation := fun (y: MatchState) =>
                          (* i. Assert: y is a MatchState. *)
                          (* ii. Return y. *)
                          y
                        in
                        (* d. Let r be m(x, d). *)
                        let! r =<< m x d in
                        (* e. If r is failure, return failure. *)
                        if r is failure then
                          failure
                        else
                        (* f. Let y be r's MatchState. *)
                        destruct! (Some y) <- r in
                        (* g. Let cap be y's captures List. *)
                        let cap := MatchState.captures y in
                        (* h. Let cap be y's captures List. *)
                        let input := MatchState.input x in
                        (* i. Let cap be y's captures List. *)
                        let xe := MatchState.endIndex x in
                        (* j. Let z be the MatchState (Input, xe, cap). *)
                        let z := match_state input xe cap in
                        (* k. Let z be the MatchState (Input, xe, cap). *)
                        c z): Matcher
  | NegativeLookahead r  => (**  Assertion :: (?! Disjunction ) *)
                      (* 1. Let m be CompileSubpattern of Disjunction with arguments rer and forward. *)
                      let! m =<< compileSubPattern r (NegativeLookahead_inner :: ctx) rer forward in
                      (* 2. Return a new Matcher with parameters (x, c) that captures m and performs the following steps when called: *)
                      (fun (x: MatchState) (c: MatcherContinuation) =>
                        (* a. Assert: x is a MatchState. *)
                        (* b. Assert: c is a MatcherContinuation. *)
                        (* c. Let d be a new MatcherContinuation with parameters (y) that captures nothing and performs the following steps when called: *)
                        let d: MatcherContinuation := fun (y: MatchState) =>
                          (* i. Assert: y is a MatchState. *)
                          (* ii. Return y. *)
                          y
                        in
                        (* d. Let r be m(x, d). *)
                        let! r =<< m x d in
                        (* e. If r is not failure, return failure. *)
                        if r is not failure then
                          failure
                        else
                        c x): Matcher
  | Lookbehind r    =>  (**  Assertion :: (?<= Disjunction ) *)
                      (* 1. Let m be CompileSubpattern of Disjunction with arguments rer and backward. *)
                      let! m =<< compileSubPattern r (Lookbehind_inner :: ctx) rer backward in
                      (* 2. Return a new Matcher with parameters (x, c) that captures m and performs the following steps when called: *)
                      (fun (x: MatchState) (c: MatcherContinuation) =>
                        (* a. Assert: x is a MatchState. *)
                        (* b. Assert: c is a MatcherContinuation. *)
                        (* c. Let d be a new MatcherContinuation with parameters (y) that captures nothing and performs the following steps when called: *)
                        let d: MatcherContinuation := fun (y: MatchState) =>
                          (* i. Assert: y is a MatchState. *)
                          (* ii. Return y. *)
                          y
                        in
                        (* d. Let r be m(x, d). *)
                        let! r =<< m x d in
                        (* e. If r is failure, return failure. *)
                        if r is failure then
                          failure
                        else
                        (* f. Let y be r's MatchState. *)
                        destruct! (Some y) <- r in
                        (* g. Let cap be y's captures List. *)
                        let cap := MatchState.captures y in
                        (* h. Let cap be y's captures List. *)
                        let input := MatchState.input x in
                        (* i. Let cap be y's captures List. *)
                        let xe := MatchState.endIndex x in
                        (* j. Let z be the MatchState (Input, xe, cap). *)
                        let z := match_state input xe cap in
                        (* k. Let z be the MatchState (Input, xe, cap). *)
                        c z): Matcher
  | NegativeLookbehind r  => (**  Assertion :: (?<! Disjunction ) *)
                      (* 1. Let m be CompileSubpattern of Disjunction with arguments rer and backward. *)
                      let! m =<< compileSubPattern r (NegativeLookbehind_inner :: ctx) rer backward in
                      (* 2. Return a new Matcher with parameters (x, c) that captures m and performs the following steps when called: *)
                      (fun (x: MatchState) (c: MatcherContinuation) =>
                        (* a. Assert: x is a MatchState. *)
                        (* b. Assert: c is a MatcherContinuation. *)
                        (* c. Let d be a new MatcherContinuation with parameters (y) that captures nothing and performs the following steps when called: *)
                        let d: MatcherContinuation := fun (y: MatchState) =>
                          (* i. Assert: y is a MatchState. *)
                          (* ii. Return y. *)
                          y
                        in
                        (* d. Let r be m(x, d). *)
                        let! r =<< m x d in
                        (* e. If r is not failure, return failure. *)
                        if r is not failure then
                          failure
                        else
                        c x): Matcher
  | BackReference de => (** AtomEscape :: DecimalEscape *)
                      (* 1. Let n be the CapturingGroupNumber of DecimalEscape. *)
                      let n := de in
                      (* 2. Assert: n ≤ rer.[[CapturingGroupsCount]]. *)
                      (* assert! (n <=? RegExp.capturingGroupsCount rer); *)
                      (* 3. Return BackreferenceMatcher(rer, n, direction).*)
                      backreferenceMatcher rer n direction
  end.

  (** 22.2.2.2 Runtime Semantics: CompilePattern
      The syntax-directed operation CompilePattern takes argument rer (a RegExp Record) and returns an
      Abstract Closure that takes a List of characters and a non-negative integer and returns a MatchResult. It is
      defined piecewise over the following productions: *)
  Definition compilePattern (r: Regex) (rer: RegExp): Result (list Character -> non_neg_integer -> MatchResult) CompileError :=
    (* 1. Let m be CompileSubpattern of Disjunction with arguments rer and forward. *)
    let! m =<< compileSubPattern r nil rer forward in
    (* 2. Return a new Abstract Closure with parameters (Input, index) that captures rer and m and performs the following steps when called: *)
    Success (fun (input: list Character) (index: non_neg_integer) =>
      (* a. Assert: Input is a List of characters. *)
      (* b. Assert: 0 ≤ index ≤ the number of elements in Input. *)
      assert! (0 <=? index)%nat && (index <=? (length input))%nat ;
      (* c. Let c be a new MatcherContinuation with parameters (y) that captures nothing and performs the following steps when called: *)
      let c: MatcherContinuation := fun (y: MatchState) =>
        (* i. Assert: y is a MatchState. *)
        (* ii. Return y. *)
        y
      in
      (* d. Let cap be a List of rer.[[CapturingGroupsCount]] undefined values, indexed 1 through rer.[[CapturingGroupsCount]]. *)
      let cap := List.repeat undefined (RegExp.capturingGroupsCount rer) in
      (* e. Let x be the MatchState (Input, index, cap). *)
      let x := match_state input (Z.of_nat index) cap in
      (* f. Return m(x, c). *)
      m x c).
End Semantics.
