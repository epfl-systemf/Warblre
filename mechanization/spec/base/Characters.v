From Coq Require Import PeanoNat List ListSet Structures.OrderedType FSets.FSetAVL NArith Bool.
From Warblre Require Import RegExpRecord Tactics List Result Numeric Typeclasses.

Import Result.Notations.
Local Open Scope result_flow.

Module CodePoint.
  Parameter type: Type.

  Record record := make_record {
    codePoint: type;
    codeUnitCount: non_neg_integer;
    isUnpairedSurrogate: bool;
  }.

  Parameter from_numeric_value: non_neg_integer -> type.
End CodePoint.
Notation CodePoint := CodePoint.type.
Notation CodePointRecord := CodePoint.record.
Notation code_point_record := CodePoint.make_record.

Module CodeUnit.
  Parameter type: Type.
  Parameter numeric_value: type -> non_neg_integer.

  Parameter is_leading_surrogate: type -> bool.
  Parameter is_trailing_surrogate: type -> bool.

  (** 11.1.3 Static Semantics: UTF16SurrogatePairToCodePoint ( lead, trail ) *)
  Definition utf16SurrogatePairToCodePoint {F: Type} `{Result.AssertionError F} (lead trail: type): Result CodePoint F :=
  (* Assert: lead is a leading surrogate and trail is a trailing surrogate. *)
  assert! is_leading_surrogate lead && is_trailing_surrogate trail ;
  (* 2. Let cp be (lead - 0xD800) × 0x400 + (trail - 0xDC00) + 0x10000. *)
  let cp := (numeric_value lead - 0xD800) * 0x400 + (numeric_value trail - 0xDC00) + 0x10000 in
  (* 3. Return the code point cp. *)
  Success (CodePoint.from_numeric_value cp).
End CodeUnit.
Notation CodeUnit := CodeUnit.type.

Module String.
  Parameter type: Type.
  Parameter eqdec: forall (l r: type), {l=r} + {l<>r}.
  Parameter length: type -> non_neg_integer.
  Parameter substring: type -> non_neg_integer -> non_neg_integer -> type.
  Parameter codeUnitAt: type -> non_neg_integer -> CodeUnit.

  Definition isEmpty (string: type) := length string == 0.

  Definition codePointAt {F: Type} `{Result.AssertionError F} (string: type) (position: non_neg_integer): Result CodePointRecord F :=
    (* 1. Let size be the length of string. *)
    let size := length string in
    (* 2. Assert: position ≥ 0 and position < size. *)
    assert! (position >=? 0) && (position <? size) ;
    (* 3. Let first be the code unit at index position within string. *)
    let first := codeUnitAt string position in
    (* 4. Let cp be the code point whose numeric value is the numeric value of first. *)
    let cp := CodePoint.from_numeric_value (CodeUnit.numeric_value first) in
    (* 5. If first is neither a leading surrogate nor a trailing surrogate, then *)
    if negb (CodeUnit.is_leading_surrogate first) && negb (CodeUnit.is_trailing_surrogate first) then
      (* a. Return the Record { [[CodePoint]]: cp, [[CodeUnitCount]]: 1, [[IsUnpairedSurrogate]]: false }. *)
      Success (code_point_record cp 1 false)
    else
    (* 6. If first is a trailing surrogate or position + 1 = size, then *)
    if CodeUnit.is_trailing_surrogate first || ((position + 1) == size) then
      (* a. Return the Record { [[CodePoint]]: cp, [[CodeUnitCount]]: 1, [[IsUnpairedSurrogate]]: true }. *)
      Success (code_point_record cp 1 true)
    else
    (* 7. Let second be the code unit at index position + 1 within string. *)
    let second := codeUnitAt string (position + 1) in
    (* 8. If second is not a trailing surrogate, then *)
    if negb (CodeUnit.is_trailing_surrogate second) then
      (* a. Return the Record { [[CodePoint]]: cp, [[CodeUnitCount]]: 1, [[IsUnpairedSurrogate]]: true }. *)
      Success (code_point_record cp 1 true)
    else
    (* 9. Set cp to UTF16SurrogatePairToCodePoint(first, second). *)
    let! cp =<< CodeUnit.utf16SurrogatePairToCodePoint first second in
    (* 10. Return the Record { [[CodePoint]]: cp, [[CodeUnitCount]]: 2, [[IsUnpairedSurrogate]]: false }. *)
    Success (code_point_record cp 2 true).
End String.
Notation String := String.type.
#[export] Instance eqdec_String: EqDec String := { eq_dec := String.eqdec; }.

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

Module Character.
  Class class type := make {
    (* The character type and its operations *)
    eq_dec: EqDec type;
    from_numeric_value: nat -> type;
    numeric_value: type -> nat;
    canonicalize: RegExpRecord -> type -> type;

    numeric_pseudo_bij: forall c, from_numeric_value (numeric_value c) = c;
    numeric_round_trip_order: forall l r, l <= r -> (numeric_value (from_numeric_value l)) <= (numeric_value (from_numeric_value r));

    from_string: String -> list type;

    set_type: CharSet.class type;

    (* Some important (sets of) characters *)
    all: list type;
    line_terminators: list type;
    digits: list type;
    white_spaces: list type;
    ascii_word_characters: list type;

    unicode_property: Type;
    unicode_property_eqdec: EqDec unicode_property;
    code_points_for: unicode_property -> list type;
  }.

  Lemma numeric_inj `{class}: forall c c', numeric_value c = numeric_value c' -> c = c'.
    intros c c' ?%(f_equal from_numeric_value).
    rewrite !numeric_pseudo_bij in *.
    assumption.
  Qed.

  Definition type {C} `{class C} := C.
End Character.
#[global] Generalizable Variable Σ.
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
Notation Character := Character.type.
Notation UnicodeProperty := Character.unicode_property.

Instance eqdec_Character {C} `{ci: CharacterInstance C}: EqDec C := Character.eq_dec.

Module Characters. Section main.
  Context `{ep: CharacterInstance Σ}.

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