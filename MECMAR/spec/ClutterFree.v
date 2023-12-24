From Warblre Require Import Result Base Patterns Notation Semantics Match Compile.

Import Result.Notations.
Local Open Scope result_flow.

(* Module ClutterFree.
  Definition regex_compile (r: Regex) (rer: RegExp)
      (P0: Compile.EarlyErrorsFree.Regex r):
      { m: list Character -> non_neg_integer -> MatchResult | Semantics.compilePattern r rer = Success m } :=
    match Semantics.compilePattern r rer as m return 
      Semantics.compilePattern r rer = m -> { m: list Character -> non_neg_integer -> MatchResult | Semantics.compilePattern r rer = Success m }
    with
    | Success v => fun eq => exist _ v eq
    | Failure CompileError.AssertionFailed => fun eq => match (Compile.Safety.compilePattern r rer) P0 eq with end
    end eq_refl.

  Definition regex_match (r: Regex) (rer: RegExp) (input: list Character) (start: non_neg_integer)
      (P0: Compile.EarlyErrorsFree.Regex r)
      (P1: Correctness.Groups.Ranges r 1 (RegExp.capturingGroupsCount rer) (RegExp.capturingGroupsCount rer))
      (P2: 0 <= start <= (length input)):
      { x: option MatchState | exists m, Semantics.compilePattern r rer = Success m /\ m input start = Success x } :=
    let (m, Eq_m) := regex_compile r rer P0 in
    match m input start as res return
      m input start = res -> { x: option MatchState | exists m, Semantics.compilePattern r rer = Success m /\ m input start = Success x }
    with
    | Success v => fun eq => exist _ v (ex_intro _ m (conj Eq_m eq))
    | out_of_fuel => fun eq => match (Correctness.Termination.compilePattern r rer input start m) Eq_m eq with end
    | match_assertion_failed => fun eq => match (Correctness.Safety.compilePattern r rer input start m) P1 P2 Eq_m eq with end
    end eq_refl.
End ClutterFree. *)