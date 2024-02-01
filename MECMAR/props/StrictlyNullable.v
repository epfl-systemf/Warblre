From Coq Require Import PeanoNat ZArith Bool Lia List.
From Warblre Require Import Tactics Focus Result Base Patterns StaticSemantics Notation List Semantics Match EarlyErrors.

Import Result.Notations.
Import Result.Notations.Boolean.
Import Coercions.
Import Semantics.
Import MatchState.
Import Match.

Local Open Scope result_flow.

(** * Stricly Nullable Static Analysis  *)

(* A regex is stricly nullable when if it matches, it always matches the empty string. It cannot match characters *)
(* The following function is a static under-approximation  of when is a regex striclty nullable. *)

Fixpoint strictly_nullable (r:Regex) : bool :=
  match r with
  | Empty | Lookahead _ | NegativeLookahead _ | Lookbehind _ | NegativeLookbehind _ => true
  | InputStart | InputEnd | WordBoundary | NotWordBoundary => true
  | Char _ | Dot | CharacterClass _ | AtomEsc _ => false
  | Disjunction r1 r2 | Seq r1 r2 => andb (strictly_nullable r1) (strictly_nullable r2)
  | Quantified r1 _ | Group _ r1 => strictly_nullable r1
  end.

(* For a few constructors, we could be more precise *)
(* For instance, for backreferences, we could track is the corresponding group is itself striclty nullable. *)
(* If it is, then so is the backreference *)
(* For the Quantifier, we could see as striclty nullable repetitions like {0} and {0,0} regardless of the inner regex *)


(** * Intermediate lemmas  *)
Lemma nil_range:
  forall x, List.Range.Nat.Bounds.range x x = nil.
Proof.
  intros x. unfold List.Range.Nat.Bounds.range, List.Range.Nat.Length.range.
  rewrite Nat.sub_diag. auto.
Qed.

Lemma update_nil:
  forall T (t:T) l,
  List.Update.Nat.Batch.update t l nil = Success l.
Proof.
  intros T t l. unfold List.Update.Nat.Batch.update. simpl. auto.
Qed.



(** * Transformation Correctness  *)
(* Correctness of the transformation that replaces the star of a strictly nullable regex with epsilon *)

(* The repeatMatcher', whether it compiles r* or empty when r is strictly nullable, *)
(* returns matchers equal matchers *)
(* this requires that rer is correct with regards to the root regex being compiled *)
Lemma strictly_nullable_repeatmatcher':
  forall (r:Regex) (root:Regex) (ctx:RegexContext) (rer:RegExp) (dir:direction) (m:Matcher)
    (STRICTLY_NULLABLE: strictly_nullable r = true)
    (COMPILE: compileSubPattern r ctx rer dir = Success m)
    (RER_ADEQUACY: countLeftCapturingParensWithin root nil = RegExp.capturingGroupsCount rer)
    (ROOT: Root root r ctx)
    (EARLY_ERRORS: EarlyErrors.Pass.Regex root nil),
  forall (x:MatchState) (c:MatcherContinuation),
    repeatMatcher' m O%nat NoI.Inf true x c (countLeftCapturingParensBefore r ctx) (countLeftCapturingParensWithin r ctx) (repeatMatcherFuel O%nat x) = c x.
Proof.
  intros r. induction r; intros root ctx rer dir m STRICTLY_NULLABLE COMPILE RER_ADEQUACY ROOT EARLY_ERRORS x c; simpl;
    try solve [inversion STRICTLY_NULLABLE];
    destruct (repeatMatcherFuel 0 x) eqn:FUEL; try solve[unfold repeatMatcherFuel in FUEL; lia].
  (* Empty *)
  - simpl in COMPILE. inversion COMPILE as [COMPILED]. clear COMPILE COMPILED.
    simpl. repeat rewrite PeanoNat.Nat.add_sub. rewrite Nat.add_0_r.
    rewrite nil_range. rewrite update_nil.
    rewrite Z.eqb_refl. simpl. auto.
  (* disjunction *)
  -
    (* I realize that induction over r is not a good idea. *)
    (* (r1|r2)* is not r1*|r2* so how do I use my Induction Hypothesis? *)
    
    
      
      Admitted.


    
Theorem strictly_nullable_same_matcher:
  forall (r:Regex) (root:Regex) (ctx:RegexContext) (rer:RegExp) (dir:direction) (mstar:Matcher) (mempty:Matcher)
    (STRICTLY_NULLABLE: strictly_nullable r = true)
    (COMPILESTAR: compileSubPattern (Quantified r (Greedy Star)) ctx rer dir = Success mstar)
    (COMPILEEMPTY: compileSubPattern Empty ctx rer dir = Success mempty)
    (RER_ADEQUACY: countLeftCapturingParensWithin root nil = RegExp.capturingGroupsCount rer)
    (ROOT: Root root r (Quantified_inner (Greedy Star) :: ctx))
    (EARLY_ERRORS: EarlyErrors.Pass.Regex root nil),
  forall (x:MatchState) (c:MatcherContinuation),
    mstar x c = mempty x c.
Proof.
  intros r root ctx rer dir mstar mempty STRICTLY_NULLABLE COMPILESTAR COMPILEEMPTY RER_ADEQUACY ROOT EARLY_ERRORS x c.
  simpl in COMPILEEMPTY. unfold Coercions.wrap_Matcher in COMPILEEMPTY. inversion COMPILEEMPTY. clear COMPILEEMPTY H0 mempty.
  simpl in COMPILESTAR. destruct (compileSubPattern r (Quantified_inner (Greedy Star) :: ctx) rer dir) as [m|] eqn:SUBSTAR.
  2: { inversion COMPILESTAR. }
  unfold Coercions.wrap_Matcher in COMPILESTAR. inversion COMPILESTAR as [STAR]. clear COMPILESTAR.
  apply strictly_nullable_repeatmatcher' with (x:=x) (c:=c) (root:=root) in SUBSTAR. 
  2: { apply STRICTLY_NULLABLE. }
  2: { apply RER_ADEQUACY. }
  2: { apply ROOT. }
  2: { apply EARLY_ERRORS. }
  simpl in SUBSTAR. rewrite PeanoNat.Nat.add_0_r in SUBSTAR.
  unfold repeatMatcher. rewrite SUBSTAR. auto.
Qed.                              
