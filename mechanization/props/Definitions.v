From Coq Require Import Bool ZArith.
From Warblre Require Import Tactics Specialize Focus Result Base Patterns Node StaticSemantics Notation Semantics Coercions.

Import Result.Notations. Local Open Scope result_flow.
Import Coercions.
Import Notation.

(* Notation for MatchStates which goes nicely with the normalization tactic *)
Notation "s '[@' n '$' c ']'" := (match_state s n c) (at level 50, left associativity).

(* Notation for the "tiny step" done in a character class matcher *)
Notation "'step{' dir '}' e " := (if dir == forward then (e + 1)%Z else (e - 1)%Z) (at level 51, right associativity).

Ltac clear_result := autounfold with result_wrappers in *; repeat match goal with
| [ E: Success _ = Success _ |- _ ] => injection E as E
| [ E: Failure _ = Failure _ |- _ ] => injection E as E
end.

Module Definitions.

  Definition characterClass_successful_state `{ep: CharacterInstance Σ} input endIndex captures (dir: Direction) := input [@ step{dir} endIndex $ captures ].

  Module RepeatMatcher.
    Definition matcher `{ep: CharacterInstance Σ} (m: Matcher) (min: non_neg_integer) (max: non_neg_integer_or_inf) 
      (greedy: bool) (parenIndex parenCount: non_neg_integer) (fuel: nat): Matcher :=
        fun (x : MatchState) (c : MatcherContinuation) => Semantics.repeatMatcher' m min max greedy x c parenIndex parenCount fuel.

    Definition continuation `{ep: CharacterInstance Σ} (x: MatchState) (c: MatcherContinuation) (m: Matcher) (min: non_neg_integer) (max: non_neg_integer_or_inf) 
      (greedy: bool) (parenIndex parenCount: non_neg_integer) (fuel: nat): MatcherContinuation :=
        fun y : MatchState =>
          if (min == 0) && (MatchState.endIndex y =? MatchState.endIndex x)%Z
          then None
          else
           Semantics.repeatMatcher' m (if min == 0 then 0 else min - 1)
             (if (max =? +∞)%NoI then +∞ else (max - 1)%NoI) greedy y c parenIndex parenCount fuel.
  End RepeatMatcher.

  Module PositiveLookaround.
    Definition matcher `{ep: CharacterInstance Σ} (m: Matcher): MatchState -> MatcherContinuation -> MatchResult :=
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
    Lemma lookahead_correctness `{ep: CharacterInstance Σ}: forall r ctx rer dir m,
      Semantics.compileSubPattern r (Lookahead_inner :: ctx) rer forward = Success m ->
      Semantics.compileSubPattern (Patterns.Lookahead r) ctx rer dir = Success (matcher m).
    Proof. intros ? ? ? ? ? H. cbn. rewrite -> H. reflexivity. Qed.
    Lemma lookbehind_correctness `{ep: CharacterInstance Σ}: forall r ctx rer dir m,
      Semantics.compileSubPattern r (Lookbehind_inner :: ctx) rer backward = Success m ->
      Semantics.compileSubPattern (Patterns.Lookbehind r) ctx rer dir = Success (matcher m).
    Proof. intros ? ? ? ? ? H. cbn. rewrite -> H. reflexivity. Qed.

  End PositiveLookaround.

  Module NegativeLookaround.
    Definition matcher `{ep: CharacterInstance Σ} (m: Matcher): MatchState -> MatcherContinuation -> MatchResult :=
      fun (x : MatchState) (c : MatcherContinuation) =>
        let d: MatcherContinuation := fun y => y in
        let! r =<< m x d in
        if r != failure then failure
        else
        c x.

    (* Check this definition *)
    Lemma negativeLookahead_correctness `{ep: CharacterInstance Σ}: forall r ctx rer dir m,
      Semantics.compileSubPattern r (NegativeLookahead_inner :: ctx) rer forward = Success m ->
      Semantics.compileSubPattern (Patterns.NegativeLookahead r) ctx rer dir = Success (matcher m).
    Proof. intros ? ? ? ? ? H. cbn. rewrite -> H. reflexivity. Qed.
    Lemma negativeLookbehind_correctness `{ep: CharacterInstance Σ}: forall r ctx rer dir m,
      Semantics.compileSubPattern r (NegativeLookbehind_inner :: ctx) rer backward = Success m ->
      Semantics.compileSubPattern (Patterns.NegativeLookbehind r) ctx rer dir = Success (matcher m).
    Proof. intros ? ? ? ? ? H. cbn. rewrite -> H. reflexivity. Qed.
  End NegativeLookaround.
End Definitions.
