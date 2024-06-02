From Coq Require Import Bool ZArith.
From Warblre Require Import Tactics Specialize Focus Result Base Errors Patterns Node StaticSemantics Notation Semantics Coercions.

Import Result.Notations. Local Open Scope result_flow.
Import Coercions.
Import Notation.

(**
    It is sometimes useful to refer to complex definitions which appear in the specification as part of bigger
    terms, and hence never get a name to refer to.

    Such definitions are defined in this file, to get more concise and understandable theorems down the line.
    When possible, we also include a lemma which acts as a sanity check: if the definition inside the spec changes 
    in a significant manner then the lemma will fail, which is easier to diagnose than a random case of a proof failing.
*)

Module Definitions.
 
  Module RepeatMatcher.
    Definition matcher `{Parameters} (m: Matcher) (min: non_neg_integer) (max: non_neg_integer_or_inf) 
      (greedy: bool) (parenIndex parenCount: non_neg_integer) (fuel: nat): Matcher :=
        fun (x : MatchState) (c : MatcherContinuation) => Semantics.repeatMatcher' m min max greedy x c parenIndex parenCount fuel.

    Definition continuation `{Parameters} (x: MatchState) (c: MatcherContinuation) (m: Matcher) (min: non_neg_integer) (max: non_neg_integer_or_inf) 
      (greedy: bool) (parenIndex parenCount: non_neg_integer) (fuel: nat): MatcherContinuation :=
        fun y : MatchState =>
          if (min == 0) && (MatchState.endIndex y =? MatchState.endIndex x)%Z
          then None
          else
           Semantics.repeatMatcher' m (if min == 0 then 0 else min - 1)
             (if (max =? +∞)%NoI then +∞ else (max - 1)%NoI) greedy y c parenIndex parenCount fuel.
  End RepeatMatcher.

  Module PositiveLookaround.
    Definition matcher `{Parameters} (m: Matcher): MatchState -> MatcherContinuation -> MatchResult :=
      fun (x : MatchState) (c : MatcherContinuation) =>
        let d: MatcherContinuation := fun y => y in
        let! r =<< m x d in
        if r == failure then failure
        else
        destruct! (Some y) <- r in
        let cap := MatchState.captures y in
        let input := MatchState.input x in
        let xe := MatchState.endIndex x in
        let z := match_state input xe cap in
        c z.

    (* Check this definition *)
    Lemma lookahead_correctness `{Parameters}: forall r ctx rer dir m,
      Semantics.compileSubPattern r (Lookahead_inner :: ctx) rer forward = Success m ->
      Semantics.compileSubPattern (Patterns.Lookahead r) ctx rer dir = Success (matcher m).
    Proof. intros ? ? ? ? ? G. cbn. rewrite -> G. reflexivity. Qed.
    Lemma lookbehind_correctness `{Parameters}: forall r ctx rer dir m,
      Semantics.compileSubPattern r (Lookbehind_inner :: ctx) rer backward = Success m ->
      Semantics.compileSubPattern (Patterns.Lookbehind r) ctx rer dir = Success (matcher m).
    Proof. intros ? ? ? ? ? G. cbn. rewrite -> G. reflexivity. Qed.

  End PositiveLookaround.

  Module NegativeLookaround.
    Definition matcher `{Parameters} (m: Matcher): MatchState -> MatcherContinuation -> MatchResult :=
      fun (x : MatchState) (c : MatcherContinuation) =>
        let d: MatcherContinuation := fun y => y in
        let! r =<< m x d in
        if r != failure then failure
        else
        c x.

    (* Check this definition *)
    Lemma negativeLookahead_correctness `{Parameters}: forall r ctx rer dir m,
      Semantics.compileSubPattern r (NegativeLookahead_inner :: ctx) rer forward = Success m ->
      Semantics.compileSubPattern (Patterns.NegativeLookahead r) ctx rer dir = Success (matcher m).
    Proof. intros ? ? ? ? ? G. cbn. rewrite -> G. reflexivity. Qed.
    Lemma negativeLookbehind_correctness `{Parameters}: forall r ctx rer dir m,
      Semantics.compileSubPattern r (NegativeLookbehind_inner :: ctx) rer backward = Success m ->
      Semantics.compileSubPattern (Patterns.NegativeLookbehind r) ctx rer dir = Success (matcher m).
    Proof. intros ? ? ? ? ? G. cbn. rewrite -> G. reflexivity. Qed.
  End NegativeLookaround.
End Definitions.
