From Coq Require Import Bool ZArith.
From Warblre Require Import Tactics Specialize Focus Result Base Patterns StaticSemantics Notation Semantics Coercions.
Import Result.Notations.

Import Coercions.

(* Notation for MatchStates which goes nicely with the normalization tactic *)
Notation "s '[@' n '$' c ']'" := (match_state s n c) (at level 50, left associativity).

(* Notation for the "tiny step" done in a character class matcher *)
Notation "'step{' dir '}' e " := (if Direction.eqb dir forward then (e + 1)%Z else (e - 1)%Z) (at level 51, right associativity).

Ltac clear_result := autounfold with result_wrappers in *; repeat match goal with
| [ E: Success _ = Success _ |- _ ] => injection E as E
| [ E: Failure _ = Failure _ |- _ ] => injection E as E
end.

Module Definitions.
  Definition characterClass_successful_state input endIndex captures (dir: direction) := input [@ step{dir} endIndex $ captures ].

  Module RepeatMatcher.
    Definition matcher (m: Matcher) (min: non_neg_integer) (max: non_neg_integer_or_inf) 
      (greedy: bool) (parenIndex parenCount: non_neg_integer) (fuel: nat): Matcher :=
        fun (x : MatchState) (c : MatcherContinuation) => Semantics.repeatMatcher' m min max greedy x c parenIndex parenCount fuel.

    Definition continuation (x: MatchState) (c: MatcherContinuation) (m: Matcher) (min: non_neg_integer) (max: non_neg_integer_or_inf) 
      (greedy: bool) (parenIndex parenCount: non_neg_integer) (fuel: nat): MatcherContinuation :=
        fun y : MatchState =>
          if (min =? 0) && (MatchState.endIndex y =? MatchState.endIndex x)%Z
          then None
          else
           Semantics.repeatMatcher' m (if min =? 0 then 0 else min - 1)
             (if (max =? +∞)%NoI then +∞ else (max - 1)%NoI) greedy y c parenIndex parenCount fuel.
  End RepeatMatcher.

  Module PositiveLookaround.
    Definition matcher (m: Matcher): MatchState -> MatcherContinuation -> MatchResult :=
      fun (x : MatchState) (c : MatcherContinuation) =>
       match m x (fun y : MatchState => (Success (Some y))) with
       | Success v =>
           if v is not (Some _)
           then Success None
           else
            match v with
            | Some y =>
                c (match_state (MatchState.input x) (MatchState.endIndex x) (MatchState.captures y))
            | None => match_assertion_failed
            end
       | Failure f => Failure f
       end.
  End PositiveLookaround.

  Module NegativeLookaround.
    Definition matcher (m: Matcher): MatchState -> MatcherContinuation -> MatchResult :=
      fun (x : MatchState) (c : MatcherContinuation) =>
       match m x (fun y : MatchState => (Success (Some y))) with
       | Success v => if v is not None then Success None else c x
       | Failure f => Failure f
       end.
  End NegativeLookaround.
End Definitions.
