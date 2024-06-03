From Warblre Require Import Result Base Errors Patterns Notation StaticSemantics Semantics Definitions EarlyErrors Compile Match RegExpRecord.

Import Result.Notations.
Local Open Scope result_flow.

(**
    This file contains combinations of key theorems.
*)

(*
    This module contains "intuitive" theorems, which are direct corrolaries from key theorems.
*)
Module Intuition.

  Lemma early_errors_compile `{Parameters}:
    (* For all regexes without early errors *)
    forall r rer (EE_free: StaticSemantics.earlyErrors r nil = Success false),
    countLeftCapturingParensWithin r nil = RegExpRecord.capturingGroupsCount rer ->
    (* compiling it to a matcher is a success *)
    exists m, Semantics.compilePattern r rer = Success m.
  Proof.
    intros.
    apply EarlyErrors.earlyErrors in EE_free. apply Compile.compilePattern with (rer := rer) in EE_free; [ | assumption ].
    (* Let's see the result of the compilation *)
    destruct (Semantics.compilePattern r rer) eqn:Eq.
    - (* Compilation succeded *)
      exists s. reflexivity.
    - (* The only possible error (f) is assertion_failed -> contradiction. *)
      destruct f. contradiction.
  Qed.

  (* The repeat matcher always terminate. *)
  Lemma repeat_matcher_terminates `{Parameters}: forall m x c min max dir rer greedy parenIndex parenCount,
    (* For any valid state *)
    Match.MatchState.Valid (Notation.MatchState.input x) rer x ->
    Match.Captures.Valid rer parenIndex parenCount ->
    (* for any continuation c that terminates *)
    forall (Termination_c: forall y, c y <> out_of_fuel),
    (* for any matcher m with the invariant *)
    Match.MatcherInvariant.matcher_invariant m dir rer ->
    (* then the matcher constructed by RepeatMatcher terminates *)
    Semantics.repeatMatcher' m min max greedy x c parenIndex parenCount (min + Match.MatchState.remainingChars x dir + 1) <> out_of_fuel.
  Proof.
    intros.
    set (fuel := min + Match.MatchState.remainingChars x dir + 1).
    enough (MI: Match.MatcherInvariant.conditional_matcher_invariant (fun x => Match.MatcherInvariant.fuelBound min x dir <= fuel) (Definitions.RepeatMatcher.matcher m min max greedy parenIndex parenCount fuel) dir rer).
    - unfold Match.MatcherInvariant.conditional_matcher_invariant in *.
      specialize (MI x c ltac:(cbn; eauto using Match.MatcherInvariant.repeatMatcherFuel_satisfies_bound) ltac:(eassumption)) as [ Eq | (? & ? & ? & Eq) ].
      + (* Matching resulted in mismatch, not out_of_fuel *)
        unfold Definitions.RepeatMatcher.matcher in Eq. rewrite -> Eq. discriminate.
      + (* The termination was called *)
        unfold Definitions.RepeatMatcher.matcher in Eq. rewrite <- Eq.
        apply Termination_c.
    - apply Match.MatcherInvariant.repeatMatcher'; assumption.
  Qed.

End Intuition.

(*
    This module ensures that all of the theorems proved "flow" into each other.
    It ensures that the post-condition of the theorem on early errors is strong enough to apply the theorem on
    compilation of regexes, which is in turn strong enough to apply the theorem on matching.
*)
Module EndToEndFunctions.
  Import Notation.
  Import Patterns.

  Definition regex_compile `{Parameters} (r: Regex) (rer: RegExpRecord)
      (P0: countLeftCapturingParensWithin r nil = RegExpRecord.capturingGroupsCount rer)
      (P1: EarlyErrors.Pass_Regex r nil):
      { m: list Character -> non_neg_integer -> MatchResult | Semantics.compilePattern r rer = Success m } :=
    match Semantics.compilePattern r rer as m return 
      Semantics.compilePattern r rer = m -> { m: list Character -> non_neg_integer -> MatchResult | Semantics.compilePattern r rer = Success m }
    with
    | Success v => fun eq => exist _ v eq
    | Error CompileError.AssertionFailed => fun eq => match (Compile.compilePattern r rer) P0 P1 eq with end
    end eq_refl.

  Definition regex_match `{Parameters} (r: Regex) (rer: RegExpRecord) (input: list Character) (start: non_neg_integer)
      (P0: countLeftCapturingParensWithin r nil = RegExpRecord.capturingGroupsCount rer)
      (P1: EarlyErrors.Pass_Regex r nil)
      (P2: start <= (length input)):
      { x: option MatchState | exists m, Semantics.compilePattern r rer = Success m /\ m input start = Success x } :=
    let (m, Eq_m) := (regex_compile r rer P0 P1) in
    match m input start as res return
      m input start = res -> { x: option MatchState | exists m, Semantics.compilePattern r rer = Success m /\ m input start = Success x }
    with
    | Success v => fun eq => exist _ v (ex_intro _ m (conj Eq_m eq))
    | out_of_fuel => fun eq => match (Match.termination r rer input start m) P1 P0 Eq_m eq with end
    | match_assertion_failed => fun eq => match (Match.no_failure r rer input start m) P1 P0 Eq_m P2 eq with end
    end eq_refl.

  Definition regex_end_to_end `{Parameters} (r: Regex) (rer: RegExpRecord) (input: list Character) (start: non_neg_integer)
      (P0: countLeftCapturingParensWithin r nil = RegExpRecord.capturingGroupsCount rer)
      (P1: start <= (length input)): option MatchState :=
    match StaticSemantics.earlyErrors r nil as ee return
      StaticSemantics.earlyErrors r nil = ee -> option MatchState
    with
    | Success false => fun eq => proj1_sig (regex_match r rer input start P0 (EarlyErrors.earlyErrors r eq) P1)
    | Success true => fun _ => None
    | Error SyntaxError.AssertionFailed => fun eq => match EarlyErrors.Safety_earlyErrors _ eq with end
    end eq_refl.
End EndToEndFunctions.