From Warblre Require Import Result Typeclasses Numeric RegExpRecord.

(**
    All parameters of the mechanization.

    This groups all of the types, functions, and theorems about them which are left abstract in the development.
    These are packed in a big module type in API.v which is then used to instantiate engines from the specification.
*)

(* Markers used to guide typechecking *)
Class CharacterMarker (T: Type): Prop := mk_character_marker {}.
Class StringMarker (T: Type): Prop := mk_string_marker {}.
Class UnicodePropertyMarker (T: Type): Prop := mk_unicode_property_marker {}.

(* Represent characters; the matching algorithm manipulates lists of such characters. *)
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

(* Represent sets of characters *)
(*>>
    22.2.2.1

    [...]
    A CharSet is a mathematical set of characters.
    In the context of a Unicode pattern, “all characters” means the CharSet containing all code point values; otherwise
    “all characters” means the CharSet containing all code unit values. 
    [...]
<<*)
Module CharSet.
  Class class `{Character.class} := make {
    type: Type;

    empty: type;
    from_list: list Character -> type;
    union: type -> type -> type;
    singleton: Character -> type;
    size: type -> nat;
    remove_all: type -> type -> type;
    is_empty: type -> bool;

    contains: type -> Character -> bool;

    range: Character -> Character -> type;

    unique: forall {F: Type} {_: Result.AssertionError F}, type -> Result Character F;
    filter: type -> (Character -> bool) -> type;
    exist: type -> (Character -> bool) -> bool;
    exist_canonicalized: RegExpRecord -> type -> Character -> bool;

    singleton_size: forall c, size (singleton c) = 1;
    singleton_exist: forall c p, exist (singleton c) p = p c;
    singleton_unique: forall {F: Type} {af: Result.AssertionError F} c, @unique F af (singleton c) = Success c;
    exist_canonicalized_equiv: forall rer s c,
      exist_canonicalized rer s c =
      exist
        s
        (fun c0 => (Character.canonicalize rer c0) == (Character.canonicalize rer c))
  }.
End CharSet.
Notation CharSet := CharSet.type.

(* Represent strings, before they are converted to lists of characters. *)
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

(* Represents unicode properties. *)
Module Property.
  Class class (char: Type) := make {
    type: Type;

    #[global] unicode_property_eqdec:: EqDec type;
    code_points_for: type -> list char;
  }.
End Property.
Notation Property := Property.type.

(* Wraps all parameters in a single parameter. *)
Module Parameters.
  Class class := make {
    #[global] character_class:: Character.class;

    #[global] set_class:: @CharSet.class character_class;
    #[global] string_class:: String.class Character.type;
    #[global] unicode_property_class:: Property.class Character.type;

    #[global] character_marker:: CharacterMarker Character.type;
    #[global] string_marker:: StringMarker String.type;
    #[global] unicode_property_marker::> UnicodePropertyMarker Property.type;
  }.
End Parameters.
Notation Parameters := @Parameters.class.

(* Used in Frontend.v due to bug in coq kernel (see call site). TODO: remove once bug is fixed. *)
Definition string_string `{Parameters}: String.class Character := Parameters.string_class.

(* Some special characters used by the specification. *)
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