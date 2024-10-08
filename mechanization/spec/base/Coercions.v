From Coq Require Import ZArith.
From Warblre Require Import Result Numeric Characters Patterns Notation Parameters.
Set Warnings "-uniform-inheritance".

(** Since the specification isn't "strongly" typed,
    we use coercions to automatically convert between types
    when the specification does this implicitly.

    Additionally, coercions are used to wrap values into the Result monad.
*)

Create HintDb result_wrappers.

Module Coercions.
  Import Notation.
  Import Patterns.

  (** These ones are used implicitly by the specification *)

  (* Numeric conversions *)
  Coercion nat_to_nni: nat >-> non_neg_integer. (* Effectively an identity *)
  Coercion Z.of_nat: nat >-> Z.
  Coercion NoI.N: non_neg_integer >-> non_neg_integer_or_inf.
  Coercion positive_to_non_neg: positive_integer >-> non_neg_integer.
  Coercion positive_to_nat: positive_integer >-> nat.

  (* Pseudo-subtyping, a.k.a. ADTs inclusion *)
  Coercion CaptureRange_or_undefined(cr: CaptureRange) := (Some cr).
  Coercion MatchState_or_failure `{Parameters} (x: MatchState) := (Some x).
  Coercion CharacterClassEscape_to_ClassEscape := fun `{Parameters} (cce: CharacterClassEscape) =>CCharacterClassEsc cce.
  Coercion CharacterEscape_to_ClassEscape := fun `{Parameters} (ce: CharacterEscape) => CCharacterEsc ce.
  Coercion ClassEscape_to_ClassAtom := fun `{Parameters} (ce: ClassEscape) => ClassEsc ce.
  Coercion ClassAtom_to_range := fun `{Parameters} (c: ClassAtom) => ClassAtomCR c EmptyCR.


  (** These ones are used to wrap things into the error monad (Result) *)
  Coercion wrap_bool := fun (F: Type) (t: bool) => @Success _ F t.
  Coercion wrap_list_Character := fun `{Parameters} (F: Type) (c: list Character) => @Success _ F c.

  Coercion wrap_option := fun (F T: Type) (t: option T) => @Success _ F t.
  Coercion wrap_Result := fun (F: Type) (v: non_neg_integer) => @Success _ F v.

  Coercion wrap_Matcher := fun `{Parameters} (F: Type) (m: Matcher) => @Success _ F m.
  Coercion wrap_CharSet := fun `{Parameters} (F: Type) (s: CharSet) => @Success _ F s.
End Coercions.

#[export]
Hint Unfold Coercions.wrap_bool Coercions.wrap_list_Character Coercions.wrap_option Coercions.wrap_Result Coercions.wrap_Matcher Coercions.wrap_CharSet: result_wrappers.