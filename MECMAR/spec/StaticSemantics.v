From Coq Require Import List.
From Warblre Require Import Base Patterns.

Module StaticSemantics.

  Fixpoint pre_order_walk (r: Regex): list Regex := match r with
  | Empty => r :: nil
  | Char _ => r :: nil
  | Disjunction r1 r2 => r :: (pre_order_walk r1 ++ pre_order_walk r2)
  | Quantified r0 _ => r :: (pre_order_walk r0)
  | Seq r1 r2 => r :: (pre_order_walk r1 ++ pre_order_walk r2)
  | Group _ r0 => r :: (pre_order_walk r0)
  | Lookahead r0 => r :: (pre_order_walk r0)
  | NegativeLookahead r0 => r :: (pre_order_walk r0)
  | Lookbehind r0 => r :: (pre_order_walk r0)
  | NegativeLookbehind r0 => r :: (pre_order_walk r0)
  | BackReference _ => r :: nil
  end.

  (** 22.2.1.1 Static Semantics: Early Errors *)
  Inductive SyntaxStatus :=
  | SyntaxOK
  | SyntaxError.

  (** 22.2.1.2 Static Semantics: CountLeftCapturingParensWithin *)
  Definition countLeftCapturingParensWithin (r: Regex): non_neg_integer := (*countLeftCapturingParensWithin_rec 0 r.*)
    List.fold_left (fun acc r => match r with
      | Group _ _ => acc + 1
      | _ => acc
      end) (pre_order_walk r) 0.

  Definition capturingGroupsWithin (r: Regex): list nat :=
    List.flat_map (fun r => match r with
      | Group id _ => id :: nil
      | _ => nil
      end) (pre_order_walk r).

  (** 22.2.1.3 Static Semantics: CountLeftCapturingParensBefore *)
(*   Fixpoint countLeftCapturingParensBefore_rec (target: Regex) (acc: non_neg_integer) (walk: list Regex): option non_neg_integer :=
    match walk with
    | nil => None
    | iter :: walk' =>
      if Regex.eqb target iter then
        Some acc
      else match iter with
        | Group _ _ => countLeftCapturingParensBefore_rec target (S acc) walk'
        | _ => countLeftCapturingParensBefore_rec target acc walk'
        end
    end.

  Definition countLeftCapturingParensBefore (node pattern: Regex): option non_neg_integer :=
    countLeftCapturingParensBefore_rec node 0 (pre_order_walk pattern). *)

  (** 22.2.1.4 Static Semantics: CapturingGroupNumber *)
End StaticSemantics.
Export StaticSemantics.