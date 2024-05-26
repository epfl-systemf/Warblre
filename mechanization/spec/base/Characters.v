From Coq Require Import PeanoNat List ListSet Structures.OrderedType FSets.FSetAVL NArith Bool.
From Warblre Require Import RegExpRecord Tactics List Result Numeric Typeclasses.

Import Result.Notations.
Local Open Scope result_flow.

Module HexDigit.
  Parameter type: Type.
  Inductive Hex4Digits := hex4 (_0 _1 _2 _3: type).
  Parameter eq_dec: EqDec type.

  Parameter to_integer: list type -> non_neg_integer.
  Definition to_integer_4 (v: Hex4Digits) := let (_0, _1, _2, _3) := v in HexDigit.to_integer (_0 :: _1 :: _2 :: _3 :: nil).
  Axiom upper_bound_2: forall d1 d2, to_integer (d1 :: d2 :: nil) < 256.
  Axiom upper_bound_4: forall d1 d2 d3 d4, to_integer (d1 :: d2 :: d3 :: d4 :: nil) < Pos.to_nat 65536.
End HexDigit.
Notation HexDigit := HexDigit.type.
Notation Hex4Digits := HexDigit.Hex4Digits.
Instance eqdec_HexDigit: EqDec HexDigit := HexDigit.eq_dec.

Module AsciiLetter.
  Parameter type: Type.
  Parameter eq_dec: EqDec type.

  Parameter numeric_value: type -> non_neg_integer.
End AsciiLetter.
Notation AsciiLetter := AsciiLetter.type.
Instance eqdec_AsciiLetter: EqDec AsciiLetter := AsciiLetter.eq_dec.

Module Unicode.
  (** TODO: Follow the spec more closely *)
  Definition utf16SurrogatePair (lead trail: non_neg_integer): non_neg_integer :=
    (* Let cp be (lead - 0xD800) × 0x400 + (trail - 0xDC00) + 0x10000. *)
    (lead - (Pos.to_nat 0xD800))*(Pos.to_nat 0x400) + (trail - (Pos.to_nat 0xDC00)) + (Pos.to_nat 0x10000).
End Unicode.

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
End CharSet.

Module String.
  Class class (type: Type) := make {
    #[global] eqdec :: EqDec type;
    length: type -> non_neg_integer;
    substring: type -> non_neg_integer -> non_neg_integer -> type;
    advanceStringIndex: type -> non_neg_integer -> non_neg_integer;
    getStringIndex: type -> non_neg_integer -> non_neg_integer;
  }.

  Definition isEmpty `{class} (string: type) := length string == 0.
End String.

Class CharacterMarker (T: Type): Prop := mk_character_marker {}.
Class StringMarker (T: Type): Prop := mk_string_marker {}.
Class UnicodePropertyMarker (T: Type): Prop := mk_unicode_property_marker {}.

Module Character.
  Class class := make {
    Character: Type;
    String: Type;

    (* The character type and its operations *)
    #[global] eq_dec :: EqDec Character;
    from_numeric_value: nat -> Character;
    numeric_value: Character -> nat;
    canonicalize: RegExpRecord -> Character -> Character;

    numeric_pseudo_bij: forall c, from_numeric_value (numeric_value c) = c;
    numeric_round_trip_order: forall l r, l <= r -> (numeric_value (from_numeric_value l)) <= (numeric_value (from_numeric_value r));

    #[global] string_ops :: String.class String;
    from_string: String -> list Character;

    set_type: CharSet.class Character;

    (* Some important (sets of) characters *)
    all: list Character;
    line_terminators: list Character;
    digits: list Character;
    white_spaces: list Character;
    ascii_word_characters: list Character;

    unicode_property: Type;
    #[global] unicode_property_eqdec:: EqDec unicode_property;
    code_points_for: unicode_property -> list Character;

    #[global] character_marker:: CharacterMarker Character;
    #[global] string_marker:: StringMarker String;
    #[global] unicode_property_marker::> UnicodePropertyMarker unicode_property;
  }.

  Lemma numeric_inj `{class}: forall c c', numeric_value c = numeric_value c' -> c = c'.
    intros c c' ?%(f_equal from_numeric_value).
    rewrite !numeric_pseudo_bij in *.
    assumption.
  Qed.
End Character.
Notation CharacterInstance := @Character.class.
Notation CharSet := (@CharSet.set_type _ Character.set_type).

(* 
    In order to get an API which is usable from both Coq and OCaml, we use a weird aliasing trick:
    The Character record (CharacterInstance) is parametrized on the type representing a character
    (rather than making that type dependent on the record), but will only be referred to using the type function
    (or rather the associated notation Character, defined just below).
    This makes the API usable on both sides in the following sense:
    - All datatypes parametrized on the character type (but not on the CharacterInstance itself) become parametrized
      by CharacterInstance, since they refer to that type through the Character notation. Coq is very good at inferring
      which CharacterInstance to use, but not so much at guessing the character type. This additional parametrization makes
      it so that Coq is able to infer that record, which then makes it trivial to infer the character type.
    - Since the type of characters is NOT a dependent type, the type is not extracted to Obj.t, hence the OCaml API
      does not require a Obj.magic galore.
*)

Notation Character := Character.Character.
Notation String := Character.String.
Notation UnicodeProperty := Character.unicode_property.

(* Used in frontend due to bug in coq kernel (see use site). TODO: remove once bug is fixed. *)
Definition string_string `{ci: CharacterInstance}: String.class String := Character.string_ops.

Module Characters. Section main.
  Context `{ep: CharacterInstance}.

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