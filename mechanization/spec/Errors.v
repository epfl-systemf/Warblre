From Warblre Require Import Typeclasses Result.

(** Types used to represent errors at different stages of the matching pipeline. *)

(* Errors which occur during the early errors phase. *)
Module SyntaxError.
  (* Weird syntax to work around https://github.com/coq/coq/issues/7424 *)
  Inductive type: let t := Type in t :=
  | AssertionFailed.
End SyntaxError.
Notation SyntaxError := SyntaxError.type.
#[refine] #[export]
Instance eqdec_syntaxError: EqDec SyntaxError := {}. decide equality. Defined.
#[export]
Instance syntax_assertion_error: Result.AssertionError SyntaxError := { f := SyntaxError.AssertionFailed }.

(* Errors which occur during the compilation phase. *)
Module CompileError.
  (* Weird syntax to work around https://github.com/coq/coq/issues/7424 *)
  Inductive type: let t := Type in t :=
  | AssertionFailed.
End CompileError.
Notation CompileError := CompileError.type.
#[refine] #[export]
Instance eqdec_compileError: EqDec CompileError := {}. decide equality. Defined.
#[export]
Instance compile_assertion_error: Result.AssertionError CompileError := { f := CompileError.AssertionFailed }.

Module MatchError.
  Inductive type :=
  | OutOfFuel
  | AssertionFailed.
End MatchError.
Notation MatchError := MatchError.type.
#[refine] #[export]
Instance eqdec_matchError: EqDec MatchError := {}. decide equality. Defined.
#[export]
Instance match_assertion_error: Result.AssertionError MatchError := { f := MatchError.AssertionFailed }.


(* Shorthands *)
Notation compile_assertion_failed := (Error CompileError.AssertionFailed).
Notation out_of_fuel := (Error MatchError.OutOfFuel).
Notation match_assertion_failed := (Error MatchError.AssertionFailed).