From Coq Require Import ZArith List.
From Warblre Require Import Result Numeric Characters Errors List.

(** 22.2.2.1 Notation *)
(* The descriptions below use the following internal data structures: *)
Module Notation.
  (*  - A CaptureRange is an ordered pair (startIndex, endIndex) that represents the range of characters included
        in a capture, where startIndex is an integer representing the start index (inclusive) of the range within
        Input, and endIndex is an integer representing the end index (exclusive) of the range within Input. For any
        CaptureRange, these indices must satisfy the invariant that startIndex ≤ endIndex. *)
  Module CaptureRange.
    Record type := make {
      startIndex: integer; (* inclusive *)
      endIndex: integer; (* exclusive *)
    }.
  End CaptureRange.
  Notation CaptureRange := CaptureRange.type.
  Notation capture_range := CaptureRange.make.

  (*  - A MatchState is an ordered triple (input, endIndex, captures) where input is a List of characters
        representing the String being matched, endIndex is an integer, and captures is a List of values, one for
        each left-capturing parenthesis in the pattern. States are used to represent partial match states in the
        regular expression matching algorithms. The endIndex is one plus the index of the last input character
        matched so far by the pattern, while captures holds the results of capturing parentheses. The nth element
        of captures is either a CaptureRange representing the range of characters captured by the nth set of
        capturing parentheses, or undefined if the nth set of capturing parentheses hasn't been reached yet. Due
        to backtracking, many States may be in use at any time during the matching process. *)
  Module MatchState. Section main.
    Context `{CharacterInstance}.

    Record type := make {
      input: list Character;
      endIndex: integer; (* one plus the index of the last input character matched so far *)
      captures: list (option CaptureRange);
    }.
  End main. End MatchState.
  Notation MatchState := MatchState.type.
  Notation match_state := MatchState.make.

(*   Arguments MatchState.input {_} {_}.
  Arguments MatchState.endIndex {_} {_}.
  Arguments MatchState.captures {_} {_}. *)

  Section main.
    Context `{CharacterInstance}.

    (* - A MatchResult is either a MatchState or the special token failure that indicates that the match failed. *)
    Definition MatchResult := Result (option MatchState) MatchError.

    (*  - A MatcherContinuation is an Abstract Closure that takes one MatchState argument and returns a
          MatchResult result. The MatcherContinuation attempts to match the remaining portion (specified by the
          closure's captured values) of the pattern against Input, starting at the intermediate state given by its
          MatchState argument. If the match succeeds, the MatcherContinuation returns the final MatchState that it
          reached; if the match fails, the MatcherContinuation returns failure. *)
    Definition MatcherContinuation := MatchState -> MatchResult.

    (*  - A Matcher is an Abstract Closure that takes two arguments—a MatchState and a MatcherContinuation—
          and returns a MatchResult result. A Matcher attempts to match a middle subpattern (specified by the
          closure's captured values) of the pattern against the MatchState's input, starting at the intermediate state
          given by its MatchState argument. The MatcherContinuation argument should be a closure that matches
          the rest of the pattern. After matching the subpattern of a pattern to obtain a new MatchState, the Matcher
          then calls MatcherContinuation on that new MatchState to test if the rest of the pattern can match as well.
          If it can, the Matcher returns the MatchState returned by MatcherContinuation; if not, the Matcher may try
          different choices at its choice points, repeatedly calling MatcherContinuation until it either succeeds or all
          possibilities have been exhausted. *)
    Definition Matcher := MatchState -> MatcherContinuation -> MatchResult.
  End main.
  Notation undefined := None (only parsing).
End Notation.