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
