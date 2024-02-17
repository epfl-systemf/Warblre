From Coq Require Import List ListSet.
From Warblre Require Import List Result Numeric.

Module HexDigit.
  Parameter type: Type.
  Parameter eqs: forall (l r: type), {l = r} + {l <> r}.

  Parameter to_integer: type -> type -> non_neg_integer.
End HexDigit.
Notation HexDigit := HexDigit.type.

Module AsciiLetter.
  Parameter type: Type.
  Parameter eqs: forall (l r: type), {l = r} + {l <> r}.

  Parameter numeric_value: type -> non_neg_integer.
End AsciiLetter.
Notation AsciiLetter := AsciiLetter.type.

Module Character.
  Parameter type: Type.
  Parameter eqs: forall (l r: type), {l = r} + {l <> r}.
  Parameter eqb: forall (l r: type), bool.
  Definition neqb (l r: type) := negb (eqb l r).

  Parameter numeric_value: type -> non_neg_integer.
  Parameter from_numeric_value: non_neg_integer -> type.
  Parameter from_ascii_letter: AsciiLetter -> type.

  Axiom numeric_inj: forall c c', Character.numeric_value c = Character.numeric_value c' -> c = c'.
  Axiom numeric_pseudo_bij: forall c, Character.from_numeric_value (Character.numeric_value c) = c.
  Axiom numeric_pseudo_bij2: forall n, Character.numeric_value (Character.from_numeric_value n) = n.

  Module Unicode.
    Parameter case_fold: type -> type.
  End Unicode.

  Definition NULL: type := Character.from_numeric_value 0.
  Definition BACKSPACE: type := Character.from_numeric_value 8.
  Definition CHARACTER_TABULATION: type := Character.from_numeric_value 9.
  Definition LINE_FEED: type := Character.from_numeric_value 10.
  Definition LINE_TABULATION: type := Character.from_numeric_value 11.
  Definition FORM_FEED: type := Character.from_numeric_value 12.
  Definition CARRIAGE_RETURN: type := Character.from_numeric_value 13.
  Definition HYPHEN_MINUS: type := Character.from_numeric_value 55.
End Character.
Notation Character := Character.type.

Module CodePoint.
  Parameter type: Type.
  Parameter to_upper_case: type -> list type.
  Parameter code_points_to_string: list type -> list Character.

  Parameter from_character: Character -> type.
  Parameter from_ascii_letter: AsciiLetter -> type.

  Parameter numeric_value: type -> non_neg_integer.

  Axiom numeric_value_from_ascii: forall l, AsciiLetter.numeric_value l = numeric_value (from_ascii_letter l).
End CodePoint.
Notation CodePoint := CodePoint.type.

Declare Scope Character_scope.
Delimit Scope Character_scope with Chr.
Infix "=?" := Character.eqb (at level 70): Character_scope.
Infix "!=?" := Character.neqb (at level 70): Character_scope.

(*  A CharSet is a mathematical set of characters. In the context of a Unicode pattern, “all characters” means
    the CharSet containing all code point values; otherwise “all characters” means the CharSet containing all
    code unit values. *)
Definition CharSet := list Character.

Module CharSet.
  Definition empty: CharSet := nil.
  Definition union (l r: CharSet): CharSet := ListSet.set_union Character.eqs l r.
  Definition singleton (c: Character): CharSet := c :: nil.
  Definition size (s: CharSet): nat := List.length s.
  Definition unique {F: Type} {_: Result.AssertionError F} (s: CharSet): Result Character F :=
    match s with
    | c :: nil => Success c
    | _ => Result.assertion_failed
    end.
  Definition remove_all (l r: CharSet): CharSet := ListSet.set_diff Character.eqs l r.
  Definition exist {F: Type} {_: Result.AssertionError F} (s: CharSet) (m: Character -> Result bool F): Result bool F :=
    List.Exists.exist s m.
  Definition is_empty (s: CharSet): bool :=
    match s with
    | nil => true
    | _ :: _ => false
    end.
  Definition filter {F: Type} {_: Result.AssertionError F} (s: CharSet) (f: Character -> Result bool F): Result CharSet F :=
    List.Filter.filter s f.

  Definition contains (s: CharSet) (c: Character): bool := ListSet.set_mem Character.eqs c s.

  Definition range (l h: nat): CharSet :=
    List.map Character.from_numeric_value (List.Range.Nat.Bounds.range l (S h)).

  Parameter all: CharSet.
  Parameter line_terminators: CharSet.
  Parameter digits: CharSet.
  Parameter white_spaces: CharSet.
  Parameter ascii_word_characters: CharSet.
End CharSet.