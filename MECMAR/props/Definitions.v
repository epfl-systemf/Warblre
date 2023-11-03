From Coq Require Import ZArith.
From Warblre Require Import Tactics Specialize Focus Result Base Patterns StaticSemantics Notation Semantics.
Import Result.Notations.

(* Notation for MatchStates which goes nicely with the normalization tactic *)
Notation "s '[@' n '$' c ']'" := (match_state s n c) (at level 50, left associativity).

(* Notation for the "tiny step" done in a character class matcher *)
Notation "'step{' dir '}' e " := (if Direction.eqb dir forward then (e + 1)%Z else (e - 1)%Z) (at level 51, right associativity).

Module Definitions.
  Definition characterClass_successful_state input endIndex captures (dir: direction) := input [@ step{dir} endIndex $ captures ].
End Definitions.
