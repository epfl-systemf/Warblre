From Warblre Require Import Typeclasses Result.

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
#[refine] Instance eqdec_compileError: EqDec CompileError := {}. decide equality. Defined.

Module MatchError.
  Inductive type :=
  | OutOfFuel
  | AssertionFailed.
End MatchError.
Notation MatchError := MatchError.type.
#[refine] Instance eqdec_matchError: EqDec MatchError := {}. decide equality. Defined.

#[export]
Instance syntax_assertion_error: Result.AssertionError SyntaxError := { f := SyntaxError.AssertionFailed }.
#[export]
Instance compile_assertion_error: Result.AssertionError CompileError := { f := CompileError.AssertionFailed }.
#[export]
Instance match_assertion_error: Result.AssertionError MatchError := { f := MatchError.AssertionFailed }.

Notation compile_assertion_failed := (Error CompileError.AssertionFailed).
Notation out_of_fuel := (Error MatchError.OutOfFuel).
Notation match_assertion_failed := (Error MatchError.AssertionFailed).