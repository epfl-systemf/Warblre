From Warblre Require Import Result Base Patterns Notation Semantics Correctness.

Module ClutterFree.
  Definition regex_match (r: Regex) (rer: RegExp) (input: list Character) (start: non_neg_integer):   
      Correctness.Groups.Ranges r 1 (RegExp.capturingGroupsCount rer) (RegExp.capturingGroupsCount rer) ->
      0 <= start <= (length input) ->
      option MatchState :=
    let res0 := Semantics.compilePattern r rer input start in 
    match res0 as res return 
        res0 = res ->
        Correctness.Groups.Ranges r 1 (RegExp.capturingGroupsCount rer) (RegExp.capturingGroupsCount rer) ->
        0 <= start <= (length input) ->
        option MatchState
    with
    | Success v => fun _ _ _ => v
    | Failure OutOfFuel => fun eq _ _ => match (Correctness.Termination.compilePattern r rer input start) eq with end
    | Failure AssertionFailed => fun eq H0 H1 => match (Correctness.Safety.compilePattern r rer input start) H0 H1 eq with end
    end eq_refl.
End ClutterFree.