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
  Inductive type: Type :=
  | a
  | b
  | c
  | d
  | e
  | f
  | g
  | h
  | i
  | j
  | k
  | l
  | m
  | n
  | o
  | p
  | q
  | r
  | s
  | t
  | u
  | v
  | w
  | x
  | y
  | z
  | A
  | B
  | C
  | D
  | E
  | F
  | G
  | H
  | I
  | J
  | K
  | L
  | M
  | N
  | O
  | P
  | Q
  | R
  | S
  | T
  | U
  | V
  | W
  | X
  | Y
  | Z.

  Definition numeric_value (l: type): non_neg_integer :=
    match l with
    | a => 97
    | b => 98
    | c => 99
    | d => 100
    | e => 101
    | f => 102
    | g => 103
    | h => 104
    | i => 105
    | j => 106
    | k => 107
    | l => 108
    | m => 109
    | n => 110
    | o => 111
    | p => 112
    | q => 113
    | r => 114
    | s => 115
    | t => 116
    | u => 117
    | v => 118
    | w => 119
    | x => 120
    | y => 121
    | z => 122
    | A => 65
    | B => 66
    | C => 67
    | D => 68
    | E => 69
    | F => 70
    | G => 71
    | H => 72
    | I => 73
    | J => 74
    | K => 75
    | L => 76
    | M => 77
    | N => 78
    | O => 79
    | P => 80
    | Q => 81
    | R => 82
    | S => 83
    | T => 84
    | U => 85
    | V => 86
    | W => 87
    | X => 88
    | Y => 89
    | Z => 90
    end.

End AsciiLetter.
Notation AsciiLetter := AsciiLetter.type.
#[refine] #[export]
Instance eqdec_AsciiLetter: EqDec AsciiLetter := {}. decide equality. Defined.

Module Unicode.
  Definition utf16SurrogatePair (lead trail: non_neg_integer): non_neg_integer :=
    (* Let cp be (lead - 0xD800) × 0x400 + (trail - 0xDC00) + 0x10000. *)
    (lead - (Pos.to_nat 0xD800))*(Pos.to_nat 0x400) + (trail - (Pos.to_nat 0xDC00)) + (Pos.to_nat 0x10000).
End Unicode.
