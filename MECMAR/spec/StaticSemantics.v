From Coq Require Import List.
From Warblre Require Import Base Result Patterns.

Import Coercions.

Module StaticSemantics.

  Fixpoint pre_order_walk (r: Regex): list Regex := match r with
  | Empty => r :: nil
  | Char _ => r :: nil
  | Dot => r :: nil
  | CharacterClass _ => r :: nil
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

  (** 22.2.1.2 Static Semantics: CountLeftCapturingParensWithin *)
  Fixpoint countLeftCapturingParensWithin_impl (r: Regex): non_neg_integer :=
    match r with
    | Empty => 0
    | Char _ => 0
    | Dot => 0
    | CharacterClass _ => 0
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

  (** 22.2.1.4 Static Semantics: CapturingGroupNumber *)

  (** 22.2.1.5 Static Semantics: IsCharacterClass *)

  (** 22.2.1.6 Static Semantics: CharacterValue *)
  Definition characterValue {F: Type} {_: Result.AssertionError F} (self: ClassAtom): Result non_neg_integer F := match self with
  (** ClassAtomNoDash :: SourceCharacter *)
  | SourceCharacter chr =>
      (* 1. Let ch be the code point matched by SourceCharacter. *)
      (*+ TODO: What is that sentence supposed to mean ?!? *)
      let ch := chr in
      (* 2. Return the numeric value of ch. *)
      Character.numeric_value ch

  (** ClassEscape :: b *)
  | ClassEsc (ClassEscape.b) =>
      (* 1. Return the numeric value of U+0008 (BACKSPACE). *)
      Character.numeric_value Characters.BACKSPACE

  (** ClassEscape :: - *)
  | ClassEsc (ClassEscape.Dash) =>
      (* 1. Return the numeric value of U+002D (HYPHEN-MINUS). *)
      Character.numeric_value Characters.HYPHEN_MINUS

  (** CharacterEscape :: ControlEscape *)
  | ClassEsc (ClassEscape.CharacterEsc (CharacterEscape.ControlEsc esc)) =>
      (* 1. Return the numeric value according to Table 63. *)
      match esc with
      | ControlEscape.t => Character.numeric_value Characters.CHARACTER_TABULATION
      | ControlEscape.n => Character.numeric_value Characters.LINE_FEED
      | ControlEscape.v => Character.numeric_value Characters.LINE_TABULATION
      | ControlEscape.f => Character.numeric_value Characters.FORM_FEED
      | ControlEscape.r => Character.numeric_value Characters.CARRIAGE_RETURN
      end

  (** CharacterEscape :: 0 *)
  | ClassEsc (ClassEscape.CharacterEsc (CharacterEscape.Zero)) =>
      (* 1. Return the MV of HexEscapeSequence. *)
      Character.numeric_value Characters.NULL

  (** CharacterEscape :: IdentityEscape *)
  | ClassEsc (ClassEscape.CharacterEsc (CharacterEscape.IdentityEsc chr)) =>
      (* 1. Let ch be the code point matched by IdentityEscape. *)
      let ch := chr in
      (* 2. Return the numeric value of ch. *)
      Character.numeric_value ch

  | _ => Result.assertion_failed
  end.

  (** 22.2.1.7 Static Semantics: GroupSpecifiersThatMatch ( thisGroupName ) *)

  (** 22.2.1.8 Static Semantics: CapturingGroupName *)

  (** 22.2.1.9 Static Semantics: RegExpIdentifierCodePoints *)

  (** 22.2.1.10 Static Semantics: RegExpIdentifierCodePoint *)
End StaticSemantics.
Export StaticSemantics.
