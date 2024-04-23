From Coq Require Import Bool PeanoNat Structures.OrderedType FSets.FSetAVL NArith ZArith.
From Warblre Require Import Typeclasses Tactics Numeric Characters Patterns RegExpRecord StaticSemantics Semantics List Result Notation Frontend.

Module UInt16.
  Parameter type: Type.
  Parameter numeric_value: type -> non_neg_integer.
  Parameter from_numeric_value: non_neg_integer -> type.
  Parameter from_ascii_letter: AsciiLetter -> type.
  Axiom lt : type -> type -> Prop.
  Parameter compare: type -> type -> Z.
  Axiom compare_spec_lt: forall l r, Z.ltb (compare l r) 0 = true -> lt l r.
  Axiom compare_spec_eq: forall l r, Z.eqb (compare l r) 0 = true -> eq l r.
  Axiom compare_spec_gt: forall l r, Z.ltb 0 (compare l r) = true -> lt r l.

  Axiom numeric_pseudo_bij: forall c, from_numeric_value (numeric_value c) = c.
  Axiom round_trip: forall l r, l <= r -> (numeric_value (from_numeric_value l)) <= (numeric_value (from_numeric_value r)).

  Module MiniOrdered <: MiniOrderedType.
    Definition t := type.

    Definition eq : t -> t -> Prop := Logic.eq.
    Definition lt : t -> t -> Prop := UInt16.lt.

    Axiom eq_refl : forall x : t, eq x x.
    Axiom eq_sym : forall x y : t, eq x y -> eq y x.
    Axiom eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.

    Axiom lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
    Axiom lt_not_eq : forall x y : t, lt x y -> ~ eq x y.

    Definition compare : forall x y : t, Compare lt eq x y.
      intros l r.
      destruct (Z.ltb (compare l r) 0) eqn:Lt.
      - apply LT. apply compare_spec_lt. assumption.
      - destruct (Z.eqb (compare l r) 0) eqn:Eq.
        + apply EQ. apply compare_spec_eq. assumption.
        + assert (forall n m : Z, n <> m -> ~ n < m -> m < n)%Z as H. {
            intros. apply not_Zeq_inf in H as [ ? | ? ]; easy.
          }
          spec_reflector Z.ltb_spec0. spec_reflector Z.eqb_spec.
          specialize H with (1 := Eq) (2 := Lt). spec_denoter Z.ltb_spec0.
          apply GT. apply compare_spec_gt. assumption.
    Defined.
  End MiniOrdered.
  Module Ordered := MOT_to_OT (MiniOrdered).
  #[export] Instance eqdec_uint16: EqDec type := { eq_dec := Ordered.eq_dec; }.

  Parameter CodePoint: Type.
  Parameter to_code_point: type -> CodePoint.
  Parameter to_upper_case: CodePoint -> list CodePoint.
  Parameter code_points_to_string: list CodePoint -> list type.
  Definition canonicalize (rer: RegExpRecord) (ch: type): type :=
    (* 2. If rer.[[IgnoreCase]] is false, return ch. *)
    if (RegExpRecord.ignoreCase rer == false) then ch
    else
    (* 3. Assert: ch is a UTF-16 code unit. *)
    (*+ TODO: what to do? *)
    (* 4. Let cp be the code point whose numeric value is the numeric value of ch. *)
    let cp := to_code_point ch in
    (* 5. Let u be the result of toUppercase(« cp »), according to the Unicode Default Case Conversion algorithm. *)
    let u := to_upper_case cp in
    (* 6. Let uStr be CodePointsToString(u). *)
    let uStr := code_points_to_string u in
    (* 7. If the length of uStr ≠ 1, return ch. *)
    (** TODO: fix *)
    match uStr with
    | cu :: nil =>
      if (numeric_value ch >=? 128) && (numeric_value cu <? 128) then ch
      else cu
    | _ => ch
    end.

  Parameter all: list type.
  Parameter line_terminators: list type.
  Parameter digits: list type.
  Parameter white_spaces: list type.
  Parameter ascii_word_characters: list type.
End UInt16.

Module Unicode.
  Parameter type: Type.
  Parameter numeric_value: type -> non_neg_integer.
  Parameter from_numeric_value: non_neg_integer -> type.
  Parameter from_ascii_letter: AsciiLetter -> type.
  Axiom lt : type -> type -> Prop.
  Parameter compare: type -> type -> Z.
  Axiom compare_spec_lt: forall l r, Z.ltb (compare l r) 0 = true -> lt l r.
  Axiom compare_spec_eq: forall l r, Z.eqb (compare l r) 0 = true -> eq l r.
  Axiom compare_spec_gt: forall l r, Z.ltb 0 (compare l r) = true -> lt r l.

  Axiom numeric_pseudo_bij: forall c, from_numeric_value (numeric_value c) = c.
  Axiom round_trip: forall l r, l <= r -> (numeric_value (from_numeric_value l)) <= (numeric_value (from_numeric_value r)).

  Module MiniOrdered <: MiniOrderedType.
    Definition t := type.

    Definition eq : t -> t -> Prop := Logic.eq.
    Definition lt : t -> t -> Prop := Unicode.lt.

    Axiom eq_refl : forall x : t, eq x x.
    Axiom eq_sym : forall x y : t, eq x y -> eq y x.
    Axiom eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.

    Axiom lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
    Axiom lt_not_eq : forall x y : t, lt x y -> ~ eq x y.

    Definition compare : forall x y : t, Compare lt eq x y.
      intros l r.
      destruct (Z.ltb (compare l r) 0) eqn:Lt.
      - apply LT. apply compare_spec_lt. assumption.
      - destruct (Z.eqb (compare l r) 0) eqn:Eq.
        + apply EQ. apply compare_spec_eq. assumption.
        + assert (forall n m : Z, n <> m -> ~ n < m -> m < n)%Z as H. {
            intros. apply not_Zeq_inf in H as [ ? | ? ]; easy.
          }
          spec_reflector Z.ltb_spec0. spec_reflector Z.eqb_spec.
          specialize H with (1 := Eq) (2 := Lt). spec_denoter Z.ltb_spec0.
          apply GT. apply compare_spec_gt. assumption.
    Defined.
  End MiniOrdered.
  Module Ordered := MOT_to_OT (MiniOrdered).
  #[export] Instance eqdec_uint16: EqDec type := { eq_dec := Ordered.eq_dec; }.

  Parameter CodePoint: Type.
  Parameter case_fold: type -> type.

  Definition canonicalize (rer: RegExpRecord) (ch: type): type :=
    (* 1. If rer.[[Unicode]] is true and rer.[[IgnoreCase]] is true, then *)
    if (RegExpRecord.ignoreCase rer == true) then
      (* a. a. If the file CaseFolding.txt of the Unicode Character Database provides a simple or common case folding mapping for ch, return the result of applying that mapping to ch. *)
      (* b. Return ch. *)
      case_fold ch
    (* 2. If rer.[[IgnoreCase]] is false, return ch. *)
    else ch.

  Parameter UnicodeProperty: Type.
  Parameter unicode_property_eqdec: forall (l r: UnicodeProperty), {l=r} + {l<>r}.
  Parameter code_points_for: UnicodeProperty -> list type.

  Parameter all: list type.
  Parameter line_terminators: list type.
  Parameter digits: list type.
  Parameter white_spaces: list type.
  Parameter ascii_word_characters: list type.
End Unicode.

Module AVL_UInt16_CharSet.
  Module M := Make (UInt16.Ordered).

  Local Definition from_list := fun ls => List.fold_left (fun s c => M.add c s) ls M.empty.

  #[refine]
  Instance instance: @CharSet.class UInt16.type := {
    set_type := M.t;

    empty := M.empty;
    from_list := from_list;
    union := fun l r => M.union l r;
    singleton := fun c => M.singleton c;
    size := fun s => M.cardinal s;
    remove_all := fun l r => M.diff l r;

    is_empty := fun s => M.is_empty s;

    contains := fun s c => M.mem c s;

    range := fun l h => from_list (List.map UInt16.from_numeric_value (List.Range.Nat.Bounds.range (UInt16.numeric_value l) (S (UInt16.numeric_value h))));

    unique := fun {F: Type} {_: Result.AssertionError F} s =>
      if (Nat.eqb (M.cardinal s) 1) then Result.Conversions.from_option (M.choose s) else Result.assertion_failed;
    filter := fun s (f: UInt16.type -> bool) => M.filter f s;
    exist := fun s (m: UInt16.type -> bool) => M.exists_ m s;
  }.
  Proof. - reflexivity. - reflexivity. Defined.
End AVL_UInt16_CharSet.

Module AVL_Unicode_CharSet.
  Module M := Make (Unicode.Ordered).

  Local Definition from_list := fun ls => List.fold_left (fun s c => M.add c s) ls M.empty.

  #[refine]
  Instance instance: @CharSet.class Unicode.type := {
    set_type := M.t;

    empty := M.empty;
    from_list := from_list;
    union := fun l r => M.union l r;
    singleton := fun c => M.singleton c;
    size := fun s => M.cardinal s;
    remove_all := fun l r => M.diff l r;

    is_empty := fun s => M.is_empty s;

    contains := fun s c => M.mem c s;

    range := fun l h => from_list (List.map Unicode.from_numeric_value (List.Range.Nat.Bounds.range (Unicode.numeric_value l) (S (Unicode.numeric_value h))));

    unique := fun {F: Type} {_: Result.AssertionError F} s =>
      if (Nat.eqb (M.cardinal s) 1) then Result.Conversions.from_option (M.choose s) else Result.assertion_failed;
    filter := fun s (f: Unicode.type -> bool) => M.filter f s;
    exist := fun s (m: Unicode.type -> bool) => M.exists_ m s;
  }.
  Proof. - reflexivity. - reflexivity. Defined.
End AVL_Unicode_CharSet.

Module Utf16CharCode.
  #[refine]
  Instance instance: Character.class UInt16.type := {
    (* The character type and its operations *)
    eq_dec := UInt16.eqdec_uint16;
    from_numeric_value := UInt16.from_numeric_value;
    numeric_value := UInt16.numeric_value;
    canonicalize := UInt16.canonicalize;

    set_type := AVL_UInt16_CharSet.instance;

    (* Some important (sets of) characters *)
    all := UInt16.all;
    line_terminators := UInt16.line_terminators;
    digits := UInt16.digits;
    white_spaces := UInt16.white_spaces;
    ascii_word_characters := UInt16.ascii_word_characters;

    unicode_property := False;
    code_points_for := fun v => match v with end;
  }.
  Proof. - apply UInt16.numeric_pseudo_bij. - apply UInt16.round_trip. - constructor. intros []. Defined.
End Utf16CharCode.

Module UnicodeCharCode.
  #[refine]
  Instance instance: Character.class Unicode.type := {
    (* The character type and its operations *)
    eq_dec := Unicode.eqdec_uint16;
    from_numeric_value := Unicode.from_numeric_value;
    numeric_value := Unicode.numeric_value;
    canonicalize := Unicode.canonicalize;

    set_type := AVL_Unicode_CharSet.instance;

    (* Some important (sets of) characters *)
    all := Unicode.all;
    line_terminators := Unicode.line_terminators;
    digits := Unicode.digits;
    white_spaces := Unicode.white_spaces;
    ascii_word_characters := Unicode.ascii_word_characters;

    unicode_property := Unicode.UnicodeProperty;
    unicode_property_eqdec := EqDec.make _ Unicode.unicode_property_eqdec;
    code_points_for := Unicode.code_points_for;
  }.
  Proof. - apply Unicode.numeric_pseudo_bij. - apply Unicode.round_trip. Defined.
End UnicodeCharCode.

Module Type Parameters.
  Parameter Character : Type.
  Parameter char_instance: Character.class Character.
End Parameters.

Module Engine (parameters: Parameters).
  (* Instanciation *)
  Definition char_instance := parameters.char_instance.
  Definition Character := parameters.Character.

  (* Utils *)
  Definition countGroups r := @StaticSemantics.countLeftCapturingParensWithin_impl _ char_instance r.

  (* API *)
  Definition compilePattern := @Semantics.compilePattern _ char_instance.
End Engine.

Module Utf16Sig <: Parameters.
  Definition char_instance := Utf16CharCode.instance.
  Definition Character: Type := UInt16.type.
End Utf16Sig.
Module Utf16Engine := Engine Utf16Sig.

Module UnicodeSig <: Parameters.
  Definition char_instance := UnicodeCharCode.instance.
  Definition Character: Type := Unicode.type.
End UnicodeSig.
Module UnicodeEngine := Engine UnicodeSig.
