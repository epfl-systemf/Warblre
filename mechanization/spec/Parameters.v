From Warblre Require Import Result Typeclasses Numeric RegExpRecord.

Class CharacterMarker (T: Type): Prop := mk_character_marker {}.
Class StringMarker (T: Type): Prop := mk_string_marker {}.
Class UnicodePropertyMarker (T: Type): Prop := mk_unicode_property_marker {}.


Module Character.
  Class class := make {
    type: Type;

    #[global] eq_dec :: EqDec type;
    from_numeric_value: nat -> type;
    numeric_value: type -> nat;
    canonicalize: RegExpRecord -> type -> type;

    (* Some important (sets of) characters *)
    all: list type;
    line_terminators: list type;
    digits: list type;
    white_spaces: list type;
    ascii_word_characters: list type;

    numeric_pseudo_bij: forall c, from_numeric_value (numeric_value c) = c;
    numeric_round_trip_order: forall l r, l <= r -> (numeric_value (from_numeric_value l)) <= (numeric_value (from_numeric_value r));
  }.

  Lemma numeric_inj `{class}: forall c c', numeric_value c = numeric_value c' -> c = c'.
    intros c c' ?%(f_equal from_numeric_value).
    rewrite !numeric_pseudo_bij in *.
    assumption.
  Qed.
End Character.
Notation Character := Character.type.

Module CharSet.
  Class class (char: Type) := make {
    type: Type;

    empty: type;
    from_list: list char -> type;
    union: type -> type -> type;
    singleton: char -> type;
    size: type -> nat;
    remove_all: type -> type -> type;
    is_empty: type -> bool;

    contains: type -> char -> bool;

    range: char -> char -> type;

    unique: forall {F: Type} {_: Result.AssertionError F}, type -> Result char F;
    filter: type -> (char -> bool) -> type;
    exist: type -> (char -> bool) -> bool;

    singleton_size: forall c, size (singleton c) = 1;
    singleton_unique: forall {F: Type} {af: Result.AssertionError F} c, @unique F af (singleton c) = Success c;
  }.
End CharSet.
Notation CharSet := CharSet.type.

Module String.
  Class class (char: Type) := make {
    type: Type;

    #[global] eqdec :: EqDec type;
    length: type -> non_neg_integer;
    substring: type -> non_neg_integer -> non_neg_integer -> type;
    advanceStringIndex: type -> non_neg_integer -> non_neg_integer;
    getStringIndex: type -> non_neg_integer -> non_neg_integer;

    to_char_list: type -> list char;
  }.

  Definition isEmpty `{class} (string: type) := length string == 0.
End String.
Notation String := String.type.

Module Property.
  Class class (char: Type) := make {
    type: Type;

    #[global] unicode_property_eqdec:: EqDec type;
    code_points_for: type -> list char;
  }.
End Property.
Notation Property := Property.type.

Module Parameters.
  Class class := make {
    #[global] character_class:: Character.class;

    #[global] set_class:: CharSet.class Character.type;
    #[global] string_class:: String.class Character.type;
    #[global] unicode_property_class:: Property.class Character.type;

    #[global] character_marker:: CharacterMarker Character.type;
    #[global] string_marker:: StringMarker String.type;
    #[global] unicode_property_marker::> UnicodePropertyMarker Property.type;
  }.
End Parameters.
Notation Parameters := @Parameters.class.

(* Used in Frontend.v due to bug in coq kernel (see use site). TODO: remove once bug is fixed. *)
Definition string_string `{Parameters}: String.class Character := Parameters.string_class.

Module Characters. Section main.
  Context `{specParameters: Parameters}.

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