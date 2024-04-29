From Coq Require Import Bool Nat.
From Warblre Require Import Typeclasses Result Return Base.

Local Open Scope nat.
Import Result.Notations.
Local Open Scope result_flow.

Module Type Utf16String.
  Parameter Utf16CodeUnit: Type.
  Parameter Utf16String: Type.
  Parameter length: Utf16String -> non_neg_integer.
  Parameter codeUnitAt: Utf16String -> non_neg_integer -> Utf16CodeUnit.
  Parameter is_leading_surrogate: Utf16CodeUnit -> bool.
  Parameter is_trailing_surrogate: Utf16CodeUnit -> bool.
End Utf16String.

Module UnicodeOps (S: Utf16String).
  Include S.

  Definition codePointAt (string: Utf16String) (position: non_neg_integer): Result (non_neg_integer * bool) MatchError :=
    (* 1. Let size be the length of string. *)
    let size := length string in
    (* 2. Assert: position ≥ 0 and position < size. *)
    assert! (position >=? 0) && (position <? size) ;
    (* 3. Let first be the code unit at index position within string. *)
    let first := codeUnitAt string position in
    (* 4. Let cp be the code point whose numeric value is the numeric value of first. *)
    (* We don't return cp, so this isn't required *)
    (* 5. If first is neither a leading surrogate nor a trailing surrogate, then *)
    if negb (is_leading_surrogate first) && negb (is_trailing_surrogate first) then
      (* a. Return the Record { [[CodePoint]]: cp, [[CodeUnitCount]]: 1, [[IsUnpairedSurrogate]]: false }. *)
      Success (1, false)
    else
    (* 6. If first is a trailing surrogate or position + 1 = size, then *)
    if is_trailing_surrogate first || ((position + 1) == size) then
      (* a. Return the Record { [[CodePoint]]: cp, [[CodeUnitCount]]: 1, [[IsUnpairedSurrogate]]: true }. *)
      Success (1, true)
    else
    (* 7. Let second be the code unit at index position + 1 within string. *)
    let second := codeUnitAt string (position + 1) in
    (* 8. If second is not a trailing surrogate, then *)
    if negb (is_trailing_surrogate second) then
      (* a. Return the Record { [[CodePoint]]: cp, [[CodeUnitCount]]: 1, [[IsUnpairedSurrogate]]: true }. *)
      Success (1, true)
    else
    (* 9. Set cp to UTF16SurrogatePairToCodePoint(first, second). *)
    (* We don't return cp, so this isn't required *)
    (* 10. Return the Record { [[CodePoint]]: cp, [[CodeUnitCount]]: 2, [[IsUnpairedSurrogate]]: false }. *)
    Success (2, false).


  (** 22.2.7.3 AdvanceStringIndex ( S, index, unicode ) *)
  Definition advanceStringIndex (S: Utf16String) (index: non_neg_integer) : Result.Result non_neg_integer MatchError :=
    (* 1. Assert: index ≤ 2^53 - 1. *)
    (* assert! (index <? 9007199254740991)%nat; *)
    (* If unicode is false, return index + 1. *)
    (* Unicode is always true *)
    (* 3. Let length be the length of S. *)
    let length := length S in
    (* 4. If index + 1 ≥ length, return index + 1. *)
    if (index + 1) >=? length then Success (index + 1) else
    (* 5. Let cp be CodePointAt(S, index). *)
    let! (codeUnitCount, _) =<< codePointAt S index in
    (* 6. Return index + cp.[[CodeUnitCount]]. *)
    Success (index + codeUnitCount)%nat.

  (** 22.2.7.4 GetStringIndex ( S, codePointIndex ) *)
  Definition getStringIndex (S: Utf16String) (codePointIndex: non_neg_integer) : Result.Result non_neg_integer MatchError :=
    (* If S is the empty String, return 0. *)
    if length S == 0 then Success 0 else
    (* 2. Let len be the length of S. *)
    let len := length S in
    (* 3. Let codeUnitCount be 0. *)
    let codeUnitCount := 0 in
    (* 4. Let codePointCount be 0. *)
    let codePointCount := 0 in
    (* 5. Repeat, while codeUnitCount < len, *)
    let! res =<< Return.while MatchError.OutOfFuel (len + 2) (codeUnitCount, codePointCount)
      (fun p => let (codeUnitCount, _) := p in codeUnitCount <? len)
      (fun p => let (codeUnitCount, codePointCount) := p in
        (* a. If codePointCount = codePointIndex, return codeUnitCount. *)
        if codePointCount == codePointIndex then Success (Return.ret codeUnitCount) else
        (* b. Let cp be CodePointAt(S, codeUnitCount). *)
        let! (cp_codeUnitCount, _) =<< codePointAt S codeUnitCount in
        (* c. Set codeUnitCount to codeUnitCount + cp.[[CodeUnitCount]]. *)
        let codeUnitCount := codeUnitCount + cp_codeUnitCount in
        (* d. Set codePointCount to codePointCount + 1. *)
        let codePointCount := codePointCount + 1 in
        Success (Return.continue (codeUnitCount, codePointCount)))
    in
    match res with
    | Return.Returned v => Success v
    | Return.Continue (codeUnitCount, codePointCount) =>
        (* 6. Return len. *)
        Success codeUnitCount
    end.
End UnicodeOps.

