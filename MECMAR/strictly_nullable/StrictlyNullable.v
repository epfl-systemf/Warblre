From Warblre Require Import Tactics Base Patterns StaticSemantics Semantics Notation Definitions Compile Match.

Import Semantics.
Import Result.Result.
Import MatchState.

(** * Stricly Nullable Static Analysis  *)

(* A regex is stricly nullable when if it matches, it always matches the empty string. It cannot match characters *)
(* The following function is a static under-approximation  of when is a regex striclty nullable. *)

Fixpoint strictly_nullable (r:Regex) : bool :=
  match r with
  | Empty | Lookahead _ | NegativeLookahead _ | Lookbehind _ | NegativeLookbehind _ => true
  | Char _ | Dot | CharacterClass _ | AtomEsc _ => false
  | Disjunction r1 r2 | Seq r1 r2 => andb (strictly_nullable r1) (strictly_nullable r2)
  | Quantified r1 _ | Group _ r1 => strictly_nullable r1
  end.

(* For a few constructors, we could be more precise *)
(* For instance, for backreferences, we could track is the corresponding group is itself striclty nullable. *)
(* If it is, then so is the backreference *)
(* For the Quantifier, we could see as striclty nullable repetitions like {0} and {0,0} regardless of the inner regex *)


(** * Correctness of the Analysis  *)

Lemma strict_null_empty:
  forall (r:Regex) (ctx:RegexContext) (rer:RegExp) (dir:direction) (m:Matcher)
    (COMPILE: compileSubPattern r ctx rer dir = Success m)
    (x:MatchState) (c:MatcherContinuation) (y:MatchState)
    (RESULT: m x c = Success (Some y)),
    endIndex y = endIndex x.
(* no that's incorrect. talk about the intermediate value, the continuation could make some progress *)
(* either define another version of the matcher invariant with an equality *)
(* or talk about a continuation that does not make progress? but then how to say later that r* and empty are the same for any continuation? *)
Proof.
Admitted.

(** * Transformation Correctness  *)
(* Correctness of the transformation that replaces the star of a strictly nullable regex with epsilon *)

Theorem strictly_nullable_transformation_correctness:
  forall (r:Regex) (ctx:RegexContext) (rer:RegExp) (dir:direction) (mstar:Matcher) (mempty:Matcher)
    (STRICTLY_NULLABLE: strictly_nullable r = true)
    (COMPILESTAR: compileSubPattern (Quantified r (Greedy Star)) ctx rer dir = Success mstar)
    (COMPILEEMPTY: compileSubPattern Empty ctx rer dir = Success mempty),
  forall (x:MatchState) (c:MatcherContinuation),
    mstar x c = mempty x c.
Proof.
Admitted.
    
