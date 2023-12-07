From Warblre Require Import Base Notation.

(** 22.2.1 Patterns *)
Module Patterns.
  Inductive QuantifierPrefix :=
  | Star
  | Plus
  | Question
  | RepExact (count: non_neg_integer)
  | RepPartialRange (min: non_neg_integer)
  | RepRange (min: non_neg_integer) (max: non_neg_integer) (inv: (min <=? max)%nat = true).

(*   Module QuantifierPrefix.
    Definition eqb (l r: QuantifierPrefix): {l = r} + {~ l = r}.
    Proof. repeat decide equality. Defined.
  End QuantifierPrefix. *)

  Inductive Quantifier :=
  | Greedy (p: QuantifierPrefix)
  | Lazy (p: QuantifierPrefix).

(*   Module Quantifier.
    Definition eqb (l r: Quantifier): {l = r} + {~ l = r}.
    Proof. decide equality; apply QuantifierPrefix.eqb. Defined.
  End Quantifier. *)

(*   Module ClassAtom.
    Definition eqb (l r: ClassAtom): {l = r} + {~ l = r}.
    Proof. decide equality. apply Character.eqb. Defined.
  End ClassAtom. *)

  Inductive ClassRanges :=
  | EmptyCR
  | AtomChar (chr: Character)
  (* Escapes: \b \w ...*)
  (*| AtomHead (atom: ClassRanges) (rem: ClassRanges)
  | RangeHead (from to: ClassRanges) (rem: ClassRanges)*).

(*   Module ClassRanges.
    Definition eqb (l r: ClassRanges): {l = r} + {~ l = r}.
    Proof. decide equality; apply ClassAtom.eqb. Defined.
  End ClassRanges. *)

  Inductive CharacterClass :=
  | PositiveCC (crs: ClassRanges)
  | NegativeCC (crs: ClassRanges).

(*   Module CharacterClass.
    Definition eqb (l r: CharacterClass): {l = r} + {~ l = r}.
    Proof. decide equality; apply ClassRanges.eqb. Defined.
  End CharacterClass. *)

  Inductive Regex :=
  | Empty
  | Char (chr: Character)
  | Disjunction (r1 r2: Regex)
  | Quantified (r: Regex) (q: Quantifier)
  | Seq (r1 r2: Regex)
  | Group (id: nat) (r: Regex)
  (* Assertions: ^ $ \b \B *)
  | Lookahead (r: Regex)
  | NegativeLookahead (r: Regex)
  | Lookbehind (r: Regex)
  | NegativeLookbehind (r: Regex)
  | BackReference (id: nat).

(*   Module Regex.
    Definition eqb (l r: Regex): {l = r} + {~ l = r}.
    Proof. decide equality; (apply CharacterClass.eqb + apply Quantifier.eqb + (repeat decide equality)). Defined.
  End Regex. *)
End Patterns.
Export Patterns.