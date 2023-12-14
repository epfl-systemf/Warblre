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
  Fixpoint countLeftCapturingParensWithin_impl (r: Regex): non_neg_integer :=
    match r with
    | Empty => 0
    | Char _ => 0
    | Disjunction r1 r2 => (countLeftCapturingParensWithin_impl r1) + (countLeftCapturingParensWithin_impl r2)
    | Quantified r0 _ => countLeftCapturingParensWithin_impl r0
    | Seq r1 r2 => (countLeftCapturingParensWithin_impl r1) + (countLeftCapturingParensWithin_impl r2)
    | Group _ r0 => 1 + (countLeftCapturingParensWithin_impl r0)
    | Lookahead r0 => countLeftCapturingParensWithin_impl r0
    | NegativeLookahead r0 => countLeftCapturingParensWithin_impl r0
    | Lookbehind r0 => countLeftCapturingParensWithin_impl r0
    | NegativeLookbehind r0 => countLeftCapturingParensWithin_impl r0
    | BackReference _ => 0
    end.
  Definition countLeftCapturingParensWithin (r: Regex) (ctx: RegexContext): non_neg_integer := countLeftCapturingParensWithin_impl r.

  (** 22.2.1.3 Static Semantics: CountLeftCapturingParensBefore *)
  Fixpoint countLeftCapturingParensBefore_impl (ctx: RegexContext): non_neg_integer :=
    match ctx with
    | nil => 0
    | h :: t => (countLeftCapturingParensBefore_impl t) + match h with
      | Disjunction_left _ => 0
      | Disjunction_right l => countLeftCapturingParensWithin_impl l
      | Quantified_inner _ => 0
      | Seq_left _ => 0
      | Seq_right l => countLeftCapturingParensWithin_impl l
      | Group_inner _ => 1
      | Lookahead_inner => 0
      | NegativeLookahead_inner => 0
      | Lookbehind_inner => 0
      | NegativeLookbehind_inner => 0
      end
    end.
  Definition countLeftCapturingParensBefore (r: Regex) (ctx: RegexContext): non_neg_integer := countLeftCapturingParensBefore_impl ctx.
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