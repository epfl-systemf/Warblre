From Warblre Require Import Result.

Module SyntaxError.
  (* https://github.com/coq/coq/issues/7424 *)
  Inductive type: let t := Type in t :=
  | AssertionFailed.
End SyntaxError.
Notation SyntaxError := SyntaxError.type.

Module CompileError.
  (* https://github.com/coq/coq/issues/7424 *)
  Inductive type: let t := Type in t :=
  | AssertionFailed.
End CompileError.
Notation CompileError := CompileError.type.

Module MatchError.
  Inductive type :=
  | OutOfFuel
  | AssertionFailed.
End MatchError.
Notation MatchError := MatchError.type.

#[export]
Instance syntax_assertion_error: Result.AssertionError SyntaxError := { f := SyntaxError.AssertionFailed }.
#[export]
Instance compile_assertion_error: Result.AssertionError CompileError := { f := CompileError.AssertionFailed }.
#[export]
Instance match_assertion_error: Result.AssertionError MatchError := { f := MatchError.AssertionFailed }.

Notation compile_assertion_failed := (Failure CompileError.AssertionFailed).
Notation failure := None (only parsing).
Notation out_of_fuel := (Failure MatchError.OutOfFuel).
Notation match_assertion_failed := (Failure MatchError.AssertionFailed).