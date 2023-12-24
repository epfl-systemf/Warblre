From Coq Require Import ZArith.
From Warblre Require Import Result Numeric Characters Patterns Notation.

Set Warnings "-uniform-inheritance".
Module Coercions.

  (** These ones are used implicitly by the specification *)

  (* Numeric conversions *)
  Coercion nat_to_nni: nat >-> non_neg_integer. (* Effectively an identity *)
  Coercion Z.of_nat: nat >-> Z.
  Coercion NoI.N: non_neg_integer >-> non_neg_integer_or_inf.
  Coercion positive_to_non_neg: positive_integer >-> non_neg_integer.
  Coercion positive_to_nat: positive_integer >-> nat.

  (* Pseudo-subtyping, a.k.a. ADTs inclusion *)
  Coercion CaptureRange_or_undefined(cr: CaptureRange) := (Some cr).
  Coercion MatchState_or_failure(x: MatchState) := (Some x).
  Coercion CharacterClassEscape_to_ClassEscape := fun (cce: CharacterClassEscape) => ClassEscape.CharacterClassEsc cce.
  Coercion CharacterEscape_to_ClassEscape := fun (ce: CharacterEscape) => ClassEscape.CharacterEsc ce.
  Coercion ClassEscape_to_ClassAtom := fun (ce: ClassEscape) => ClassEsc ce.
  Coercion ClassAtom_to_range := fun (c: ClassAtom) => ClassAtomCR c EmptyCR.


  (** These ones are used to wrap things into the error monad (Result) *)
  Coercion wrap_bool := fun (F: Type) (t: bool) => @Success _ F t.
  Coercion wrap_Character := fun (F: Type) (c: Character) => @Success _ F c.

  Coercion wrap_option := fun (F T: Type) (t: option T) => @Success _ F t.
  Coercion wrap_Result := fun (F: Type) (v: non_neg_integer) => @Success _ F v.

  Coercion wrap_Matcher := fun (F: Type) (m: Matcher) => @Success _ F m.
  Coercion wrap_CharSet := fun (F: Type) (s: CharSet) => @Success _ F s.
End Coercions.