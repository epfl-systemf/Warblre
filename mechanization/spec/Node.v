From Coq Require Import List.
From Warblre Require Import List Result Typeclasses Base Notation Numeric Characters Patterns.

(* 
    The spec uses the notion of 'Node' to refer to an element of the parse tree.
    We represent this using a Zipper, pairing a Regex tree (i.e. a pattern without a context)
    and a context, which gives information about the Regex/parse tree this pattern is part of.

    Together, these two emulate a Regex with a backpointer to its parent.
    Hence, we call a pair (Regex, Context) a (Regex)Node.
*)
Import Patterns.

Section Zipper.
  Context `{specParameters: Parameters}.

  Inductive RegexContextLayer :=
  | Disjunction_left (r: Regex)
  | Disjunction_right (l: Regex)
  | Quantified_inner (q: Quantifier)
  | Seq_left (r: Regex)
  | Seq_right (l: Regex)
  | Group_inner (name: option GroupName)
  | Lookahead_inner
  | NegativeLookahead_inner
  | Lookbehind_inner
  | NegativeLookbehind_inner.
  Notation RegexContext := (list RegexContextLayer).
  Notation RegexNode := (Regex * RegexContext)%type.

  Definition zip_one (focus: Regex) (ctx: RegexContextLayer) := match ctx with
  | Disjunction_left r => Disjunction focus r
  | Disjunction_right l => Disjunction l focus
  | Quantified_inner q => Quantified focus q
  | Seq_left r => Seq focus r
  | Seq_right l => Seq l focus
  | Group_inner name => Group name focus
  | Lookahead_inner => Lookahead focus
  | NegativeLookahead_inner => NegativeLookahead focus
  | Lookbehind_inner => Lookbehind focus
  | NegativeLookbehind_inner => NegativeLookbehind focus
  end.

  Fixpoint zip (focus: Regex) (ctx: RegexContext): Regex :=
    match ctx with
    | nil => focus
    | h :: t => zip (zip_one focus h) t
    end.

  Definition Root (root: Regex) (r: RegexNode) := root = zip (fst r) (snd r).

  Section EqDec.
    #[export] #[refine] Instance eqdec_RegexContextLayer: EqDec RegexContextLayer := {}.
      decide equality; try apply EqDec.eq_dec. Defined.
    #[export] #[refine] Instance eqdec_RegexContext: EqDec RegexContext := {}.
      decide equality; apply EqDec.eq_dec. Defined.
    #[export] #[refine] Instance eqdec_RegexNode: EqDec RegexNode := {}.
      decide equality; apply EqDec.eq_dec. Defined.
  End EqDec.
End Zipper.
Notation RegexContext := (list RegexContextLayer).
Notation RegexNode := (Regex * RegexContext)%type.