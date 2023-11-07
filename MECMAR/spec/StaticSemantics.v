From Warblre Require Import Base Patterns.

Module StaticSemantics.
  (** 22.2.1.1 Static Semantics: Early Errors *)
  Inductive SyntaxStatus :=
  | SyntaxOK
  | SyntaxError.

  (** 22.2.1.2 Static Semantics: CountLeftCapturingParensWithin *)
  Fixpoint capturingGroupsWithin (r: Regex): IdSet.t := match r with
  | Empty => IdSet.empty
  | Char _ _ => IdSet.empty
  | Disjunction r1 r2 => IdSet.union (capturingGroupsWithin r1) (capturingGroupsWithin r2)
  | Quantified r _ => capturingGroupsWithin r
  | Seq r1 r2 => IdSet.union (capturingGroupsWithin r1) (capturingGroupsWithin r2)
  | Group id r => IdSet.add id (capturingGroupsWithin r)
  | Lookback r => capturingGroupsWithin r
  | Lookahead r => capturingGroupsWithin r
  end.

  (** 22.2.1.3 Static Semantics: CountLeftCapturingParensBefore *)

  (** 22.2.1.4 Static Semantics: CapturingGroupNumber *)
End StaticSemantics.
Export StaticSemantics.