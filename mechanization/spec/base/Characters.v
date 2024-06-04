From Coq Require Import PeanoNat List ListSet Structures.OrderedType FSets.FSetAVL NArith Bool.
From Warblre Require Import RegExpRecord Tactics List Result Numeric Typeclasses.

Import Result.Notations.
Local Open Scope result_flow.

(** Types to represent and operations to manipulate basic character type. *)

Module HexDigit.
  Inductive type: Type :=
  | Zero
  | One
  | Two
  | Three
  | Four
  | Five
  | Six
  | Seven
  | Eight
  | Nine
  | A
  | B
  | C
  | D
  | E
  | F.

  Inductive Hex4Digits := hex4 (_0 _1 _2 _3: type).

  Definition to_integer (hex: type): non_neg_integer :=
    match hex with
    | Zero  => 0
    | One   => 1
    | Two   => 2
    | Three => 3
    | Four  => 4
    | Five  => 5
    | Six   => 6
    | Seven => 7
    | Eight => 8
    | Nine  => 9
    | A     => 10
    | B     => 11
    | C     => 12
    | D     => 13
    | E     => 14
    | F     => 15
    end.

  Definition to_integer_2 (h l: type) :=
    let r0 := to_integer h in
    let r1 := (r0 * 16) + (to_integer l) in
    r1.

  Definition to_integer_4 (v: Hex4Digits) :=
    let (_0, _1, _2, _3) := v in
    let r0 := to_integer _0 in
    let r1 := (r0 * 16) + (to_integer _1) in
    let r2 := (r1 * 16) + (to_integer _2) in
    let r3 := (r2 * 16) + (to_integer _3) in
    r3.

End HexDigit.
Notation HexDigit := HexDigit.type.
Notation Hex4Digits := HexDigit.Hex4Digits.
#[refine] #[export]
Instance eqdec_HexDigit: EqDec HexDigit := {}. decide equality. Defined.

Module AsciiLetter.
  Parameter type: Type.
  Parameter eq_dec: EqDec type.

  Parameter numeric_value: type -> non_neg_integer.
End AsciiLetter.
Notation AsciiLetter := AsciiLetter.type.
Instance eqdec_AsciiLetter: EqDec AsciiLetter := AsciiLetter.eq_dec.

Module Unicode.
  Definition utf16SurrogatePair (lead trail: non_neg_integer): non_neg_integer :=
    (* Let cp be (lead - 0xD800) × 0x400 + (trail - 0xDC00) + 0x10000. *)
    (lead - (Pos.to_nat 0xD800))*(Pos.to_nat 0x400) + (trail - (Pos.to_nat 0xDC00)) + (Pos.to_nat 0x10000).
End Unicode.
