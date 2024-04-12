From Warblre Require Import Result Base Patterns Notation StaticSemantics Semantics EarlyErrors Compile Match RegExpRecord.

Import Result.Notations.
Local Open Scope result_flow.

Module ClutterFree.
  Import Notation.
  Import Patterns.

  Definition regex_compile {Character} `{ep: CharacterInstance Character} (r: Regex) (rer: RegExpRecord)
      (P0: countLeftCapturingParensWithin r nil = RegExpRecord.capturingGroupsCount rer)
      (P1: EarlyErrors.Pass_Regex r nil):
      { m: list Character -> non_neg_integer -> MatchResult | Semantics.compilePattern r rer = Success m } :=
    match Semantics.compilePattern r rer as m return 
      Semantics.compilePattern r rer = m -> { m: list Character -> non_neg_integer -> MatchResult | Semantics.compilePattern r rer = Success m }
    with
    | Success v => fun eq => exist _ v eq
    | Failure CompileError.AssertionFailed => fun eq => match (Compile.compilePattern r rer) P0 P1 eq with end
    end eq_refl.

  Definition regex_match {Character} `{ep: CharacterInstance Character} (r: Regex) (rer: RegExpRecord) (input: list Character) (start: non_neg_integer)
      (P0: countLeftCapturingParensWithin r nil = RegExpRecord.capturingGroupsCount rer)
      (P1: EarlyErrors.Pass_Regex r nil)
      (P2: start <= (length input)):
      { x: option MatchState | exists m, Semantics.compilePattern r rer = Success m /\ m input start = Success x } :=
    let (m, Eq_m) := (regex_compile r rer P0 P1) in
    match m input start as res return
      m input start = res -> { x: option MatchState | exists m, Semantics.compilePattern r rer = Success m /\ m input start = Success x }
    with
    | Success v => fun eq => exist _ v (ex_intro _ m (conj Eq_m eq))
    | out_of_fuel => fun eq => match (Correctness.termination r rer input start m) P1 P0 Eq_m eq with end
    | match_assertion_failed => fun eq => match (Correctness.no_failure r rer input start m) P1 P0 Eq_m P2 eq with end
    end eq_refl.

  Definition regex_end_to_end {Character} `{ep: CharacterInstance Character} (r: Regex) (rer: RegExpRecord) (input: list Character) (start: non_neg_integer)
      (P0: countLeftCapturingParensWithin r nil = RegExpRecord.capturingGroupsCount rer)
      (P1: start <= (length input)): option MatchState :=
    match StaticSemantics.earlyErrors r nil as ee return
      StaticSemantics.earlyErrors r nil = ee -> option MatchState
    with
    | Success false => fun eq => proj1_sig (regex_match r rer input start P0 (EarlyErrors.earlyErrors r eq) P1)
    | Success true => fun _ => None
    | Failure SyntaxError.AssertionFailed => fun eq => match EarlyErrors.Safety_earlyErrors _ eq with end
    end eq_refl.
End ClutterFree.