From Coq Require Import List.
From Warblre Require Import Result Base Patterns.

(** 22.2.2.1 Notation *)
Module Notation.

  Module CaptureRange.
    Record type := make {
      startIndex: non_neg_integer; (* inclusive *)
      endIndex: non_neg_integer; (* exclusive *)

(*           invariant: startIndex <= endIndex; *)
    }.

    Module Exports.
      Notation CaptureRange := type.
      Notation capture_range := make.
    End Exports.
  End CaptureRange.
  Export CaptureRange.Exports.

  Module MatchState.
    Record type := make {
      input: list Character;
      endIndex: non_neg_integer; (* one plus the index of the last input character matched so far *)
      captures: DMap.t CaptureRange;
    }.

(*         Definition remainingCharsCount (x: type) := (length (input x)) - (endIndex x). *)

    Module Exports.
      Notation MatchState := type.
      Notation match_state := make.
    End Exports.
  End MatchState.
  Export MatchState.Exports.

  (* «  The nth element of captures is either a CaptureRange representing 
        the range of characters captured by the nth set of capturing parentheses, 
        or undefined if the nth set of capturing parentheses hasn't been reached 
        yet. » 
        This sounds imprecise: the capture group may have been reached, but reset
  *)

  Notation "ls '[' i ']'" := (match nth_error ls i with
  | Some x => Success x
  | None => assertion_failed
  end) (at level 98, left associativity).

  Inductive Failures :=
  | Mismatch
  | OutOfFuel
  | AssertionFailed.

  Definition MatchResult := Result MatchState Failures.
  #[export]
  Instance assertion_error: AssertionError Failures := { f := AssertionFailed }.
  Notation failure := (Failure Mismatch).
  Notation out_of_fuel := (Failure OutOfFuel).

  Definition MatcherContinuation := MatchState -> MatchResult.

  Definition Matcher := MatchState -> MatcherContinuation -> MatchResult.

  (** 22.2.2.1.1 RegExp Records *)
  Record RegExp := {
  }.

  Inductive direction :=
  | forward
  | backward
  .

  Module Direction.
    Definition eqb (lhs rhs: direction): bool := match lhs, rhs with
    | forward, forward => true
    | backward, backward => true
    | _, _ => false
    end.
  End Direction.
End Notation.