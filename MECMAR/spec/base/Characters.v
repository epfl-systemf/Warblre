From Coq Require Import PeanoNat List ListSet Structures.OrderedType FSets.FSetAVL NArith.
From Warblre Require Import RegExp Tactics List Result Numeric Typeclasses.

Module HexDigit.
  Parameter type: Type.
  Parameter eq_dec: EqDec type.

  Parameter to_integer: type -> type -> non_neg_integer.
  Axiom upper_bound: forall d1 d2, to_integer d1 d2 < 256.
End HexDigit.
Notation HexDigit := HexDigit.type.
Instance eqdec_HexDigit: EqDec HexDigit := HexDigit.eq_dec.

Module AsciiLetter.
  Parameter type: Type.
  Parameter eq_dec: EqDec type.

  Parameter numeric_value: type -> non_neg_integer.
End AsciiLetter.
Notation AsciiLetter := AsciiLetter.type.
Instance eqdec_AsciiLetter: EqDec AsciiLetter := AsciiLetter.eq_dec.

Module CharSet.
  Class class (type: Type) := make {
    set_type: Type;

    empty: set_type;
    from_list: list type -> set_type;
    union: set_type -> set_type -> set_type;
    singleton: type -> set_type;
    size: set_type -> nat;
    remove_all: set_type -> set_type -> set_type;
    is_empty: set_type -> bool;

    contains: set_type -> type -> bool;

    range: type -> type -> set_type;

    unique: forall {F: Type} {_: Result.AssertionError F}, set_type -> Result type F;
    filter: set_type -> (type -> bool) -> set_type;
    exist: set_type -> (type -> bool) -> bool;

    singleton_size: forall c, size (singleton c) = 1;
    singleton_unique: forall {F: Type} {af: Result.AssertionError F} c, @unique F af (singleton c) = Success c;
  }.

  Module Parametrized.
    Class class (type set_type: Type) := make {
        empty: set_type;
        from_list: list type -> set_type;
        union: set_type -> set_type -> set_type;
        singleton: type -> set_type;
        size: set_type -> nat;
        remove_all: set_type -> set_type -> set_type;
        is_empty: set_type -> bool;

        contains: set_type -> type -> bool;

        range: type -> type -> set_type;

        unique: forall {F: Type} {_: Result.AssertionError F}, set_type -> Result type F;
        filter: set_type -> (type -> bool) -> set_type;
        exist: set_type -> (type -> bool) -> bool;

        singleton_size: forall c, size (singleton c) = 1;
        singleton_unique: forall {F: Type} {af: Result.AssertionError F} c, @unique F af (singleton c) = Success c;
      }.

      Definition unparametrize {Character T: Type} (p: class Character T): @CharSet.class Character := @CharSet.make
        Character T empty from_list union singleton size remove_all is_empty contains range (@unique Character T p) filter exist singleton_size (@singleton_unique Character T p).
  End Parametrized.
  Definition from_parametrized {Character T: Type} (p: Parametrized.class Character T): @class Character := @Parametrized.unparametrize Character T p.
End CharSet.

Module Character.
  Class class := make {
    (* The character type and its operations *)
    type: Type;
    eq_dec: EqDec type;
    from_numeric_value: nat -> type;
    numeric_value: type -> nat;
    canonicalize: RegExp -> type -> type;

    numeric_pseudo_bij: forall c, from_numeric_value (numeric_value c) = c;
    numeric_pseudo_bij2: forall n, n < Pos.to_nat 65536 -> numeric_value (from_numeric_value n) = n;

    set_type: CharSet.class type;

    (* Some important (sets of) characters *)
    all: list type;
    line_terminators: list type;
    digits: list type;
    white_spaces: list type;
    ascii_word_characters: list type;
  }.

  Lemma numeric_inj `{class}: forall c c', numeric_value c = numeric_value c' -> c = c'.
    intros c c' ?%(f_equal from_numeric_value).
    rewrite !numeric_pseudo_bij in *.
    assumption.
  Qed.

End Character.
Notation CharacterInstance := @Character.class.
Notation CharSet := (@CharSet.set_type _ Character.set_type).
Notation Character := Character.type.

Instance eqdec_Character `{ci: CharacterInstance}: EqDec Character := Character.eq_dec.

Module Characters. Section main.
  Context `{CharacterInstance}.

  Definition NULL: Character := Character.from_numeric_value 0.
  Definition BACKSPACE: Character := Character.from_numeric_value 8.
  Definition CHARACTER_TABULATION: Character := Character.from_numeric_value 9.
  Definition LINE_FEED: Character := Character.from_numeric_value 10.
  Definition LINE_TABULATION: Character := Character.from_numeric_value 11.
  Definition FORM_FEED: Character := Character.from_numeric_value 12.
  Definition CARRIAGE_RETURN: Character := Character.from_numeric_value 13.
  Definition HYPHEN_MINUS: Character := Character.from_numeric_value 55.

  Definition all: CharSet := CharSet.from_list Character.all.
  Definition line_terminators: CharSet := CharSet.from_list Character.line_terminators.
  Definition digits: CharSet := CharSet.from_list Character.digits.
  Definition white_spaces: CharSet := CharSet.from_list Character.white_spaces.
  Definition ascii_word_characters: CharSet := CharSet.from_list Character.ascii_word_characters.
End main. End Characters.