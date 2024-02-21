From Coq Require Import PeanoNat List ListSet Structures.OrderedType FSets.FSetAVL.
From Warblre Require Import Tactics List Result Numeric.

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
  Parameter numeric_value: type -> non_neg_integer.
  Parameter from_numeric_value: non_neg_integer -> type.
  Parameter from_ascii_letter: AsciiLetter -> type.
  Axiom lt : type -> type -> Prop.
  Parameter compare: type -> type -> nat.
  Axiom compare_spec_lt: forall l r, Nat.ltb (compare l r) 0 = true -> lt l r.
  Axiom compare_spec_eq: forall l r, Nat.eqb (compare l r) 0 = true -> eq l r.
  Axiom compare_spec_gt: forall l r, Nat.ltb 0 (compare l r) = true -> lt r l.

  Module MiniOrdered <: MiniOrderedType.
    Definition t := type.

    Definition eq : t -> t -> Prop := Logic.eq.
    Definition lt : t -> t -> Prop := Character.lt.

    Axiom eq_refl : forall x : t, eq x x.
    Axiom eq_sym : forall x y : t, eq x y -> eq y x.
    Axiom eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.

    Axiom lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
    Axiom lt_not_eq : forall x y : t, lt x y -> ~ eq x y.

    Definition compare : forall x y : t, Compare lt eq x y.
      intros l r.
      destruct (Nat.ltb (compare l r) 0) eqn:Lt.
      - apply LT. apply compare_spec_lt. assumption.
      - destruct (Nat.eqb (compare l r) 0) eqn:Eq.
        + apply EQ. apply compare_spec_eq. assumption.
        + assert (forall n m : nat, n <> m -> ~ n < m -> m < n) as H. {
            intros. apply Lt.nat_total_order_stt in H as [? | ?]; easy.
          }
          spec_reflector Nat.ltb_spec0. spec_reflector Nat.eqb_spec.
          specialize H with (1 := Eq) (2 := Lt). spec_denoter Nat.ltb_spec0.
          apply GT. apply compare_spec_gt. assumption.
    Defined.
  End MiniOrdered.
  Module Ordered := MOT_to_OT (MiniOrdered).

  Definition eqs: forall (l r: type), {l = r} + {l <> r} := Ordered.eq_dec.
  Definition eqb: forall (l r: type), bool := fun l r => if eqs l r then true else false.
  Definition neqb (l r: type) := negb (eqb l r).

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

  Parameter all: list type.
  Parameter line_terminators: list type.
  Parameter digits: list type.
  Parameter white_spaces: list type.
  Parameter ascii_word_characters: list type.
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
Module CharSet.
  Module M := Make (Character.Ordered).

  Definition type := M.t.

  Definition empty: type := M.empty.
  Definition from_list (ls: list Character): type := List.fold_left (fun s c => M.add c s) ls empty.
  Definition union (l r: type): type := M.union l r.
  Definition singleton (c: Character): type := M.singleton c.
  Definition size (s: type): nat := M.cardinal s.
  Definition remove_all (l r: type): type := M.diff l r.
  Definition is_empty (s: type): bool := M.is_empty s.

  Definition contains (s: type) (c: Character): bool := M.mem c s.

  Definition range (l h: nat): type := from_list (List.map Character.from_numeric_value (List.Range.Nat.Bounds.range l (S h))).

  Definition unique {F: Type} {_: Result.AssertionError F} (s: type): Result Character F :=
    if (Nat.eqb (size s) 1) then Result.Conversions.from_option (M.choose s) else Result.assertion_failed.
  Definition filter {F: Type} {_: Result.AssertionError F} (s: type) (f: Character -> bool): type := M.filter f s.
  Definition exist {F: Type} {_: Result.AssertionError F} (s: type) (m: Character -> bool): bool := M.exists_ m s.

  Definition all: type := from_list Character.all.
  Definition line_terminators: type := from_list Character.line_terminators.
  Definition digits: type := from_list Character.digits.
  Definition white_spaces: type := from_list Character.white_spaces.
  Definition ascii_word_characters: type := from_list Character.ascii_word_characters.
End CharSet.
Notation CharSet := CharSet.type.