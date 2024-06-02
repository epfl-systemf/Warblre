From Coq Require Import Bool Nat.
From Warblre Require Import Base Errors Result Return RegExpRecord Patterns Notation Semantics Frontend.

Module API.
  Module Patterns := Patterns.

  (* Packs all parameters in a module type which can easily be instantiated in OCaml. *)
  Module Type EngineParameters.
    Parameter character : Type.
    Module Character.
      Parameter equal: forall (l r: character), {l=r} + {l<>r}.
      Parameter from_numeric_value: nat -> character.
      Parameter numeric_value: character -> nat.
      Parameter canonicalize: RegExpRecord -> character -> character.

      Axiom numeric_pseudo_bij: forall c, from_numeric_value (numeric_value c) = c.
      Axiom numeric_round_trip_order: forall l r, l <= r -> (numeric_value (from_numeric_value l)) <= (numeric_value (from_numeric_value r)).
    End Character.

    Parameter string : Type.
    Module String.
      Parameter equal: forall (l r: string), {l=r} + {l<>r}.
      Parameter length: string -> non_neg_integer.
      Parameter substring: string -> non_neg_integer -> non_neg_integer -> string.
      Parameter advanceStringIndex: string -> non_neg_integer -> non_neg_integer.
      Parameter getStringIndex: string -> non_neg_integer -> non_neg_integer.
      Parameter list_from_string: string -> list character.
      Parameter list_to_string: list character -> string.
    End String.

    (** CharSet *)
    Parameter char_set: Type.

    Module CharSet.
      Parameter empty: char_set.
      Parameter from_list: list character -> char_set.
      Parameter union: char_set -> char_set -> char_set.
      Parameter singleton: character -> char_set.
      Parameter size: char_set -> nat.
      Parameter remove_all: char_set -> char_set -> char_set.
      Parameter is_empty: char_set -> bool.
      Parameter contains: char_set -> character -> bool.
      Parameter range: character -> character -> char_set.

      Parameter unique: forall (F: Type) (_: Result.AssertionError F), char_set -> Result character F.
      Parameter filter: char_set -> (character -> bool) -> char_set.
      Parameter exist_canonicalized: RegExpRecord -> char_set -> character -> bool.

      Axiom singleton_size: forall c, size (singleton c) = 1.
      Axiom singleton_unique: forall (F: Type) (af: Result.AssertionError F) c, @unique F af (singleton c) = Success c.
    End CharSet.

    Module CharSets.
      Parameter all: list character.
      Parameter line_terminators: list character.
      Parameter digits: list character.
      Parameter white_spaces: list character.
      Parameter ascii_word_characters: list character.
    End CharSets.

    Parameter property: Type.
    Module Property.
      Parameter equal: forall (l r: property), {l=r} + {l<>r}.
      Parameter code_points: property -> list character.
    End Property.
  End EngineParameters.

  (* Functor producing a fully executable engine. *)
  Module Engine (P: EngineParameters).
    Definition character := P.character.
    Definition string := P.string.
    Definition property := P.property.

    Instance character_marker: CharacterMarker character := (mk_character_marker _).
    Instance string_marker: StringMarker string := (mk_string_marker _).
    Instance property_marker: UnicodePropertyMarker property := (mk_unicode_property_marker _).

    (* Instantiation *)
    Definition parameters: Parameters := Parameters.make
      (Character.make
        character
        (EqDec.make _ P.Character.equal)
        P.Character.from_numeric_value
        P.Character.numeric_value
        P.Character.canonicalize
        P.CharSets.all
        P.CharSets.line_terminators
        P.CharSets.digits
        P.CharSets.white_spaces
        P.CharSets.ascii_word_characters
        P.Character.numeric_pseudo_bij
        P.Character.numeric_round_trip_order)
      (CharSet.make character
        P.char_set
        P.CharSet.empty
        P.CharSet.from_list
        P.CharSet.union
        P.CharSet.singleton
        P.CharSet.size
        P.CharSet.remove_all
        P.CharSet.is_empty
        P.CharSet.contains
        P.CharSet.range
        P.CharSet.unique
        P.CharSet.filter
        P.CharSet.exist_canonicalized
        P.CharSet.singleton_size
        P.CharSet.singleton_unique)
      (String.make character
        string
        (EqDec.make _ P.String.equal)
        P.String.length
        P.String.substring
        P.String.advanceStringIndex
        P.String.getStringIndex
        P.String.list_from_string)
      (Property.make character
        property
        (EqDec.make _ P.Property.equal)
        P.Property.code_points)
      _ _ _.

    (*  In order to get a strongly typed (as in: without any Obj.t) API in OCaml,
        dependent types (on the Parameters argument) must be eliminated.
        This is done by providing equivalent, yet non-depent signatures for all functions
        exposed in this API.
    *)
    Notation Regex := (@Patterns.Regex character string property _ _ _).
    Notation MatchResult := (@Notation.MatchResult character _).
    Notation RegExpInstance := (@RegExpInstance.type _ _ _ _ _ _).
    Notation ExecResult := (@ExecResult character string property _ _ _).
    Notation ProtoMatchResult := (@ProtoMatchResult character string property _ _ _).

    (* API *)
    Definition countGroups: Regex -> non_neg_integer :=
      @StaticSemantics.countLeftCapturingParensWithin_impl parameters.

    Definition compilePattern:
        Regex -> (RegExpRecord.type) ->
        Result (list character -> non_neg_integer -> MatchResult) _
      := @Semantics.compilePattern parameters.

    Definition initialize: Regex -> RegExpFlags.type -> (Result RegExpInstance _) :=
      @Frontend.regExpInitialize parameters.
    Definition setLastIndex :=
      @Frontend.RegExpInstance.setLastIndex character string property _ _ _.
    Definition execArrayExotic := @Frontend.ExecArrayExotic string (mk_string_marker _).
    Definition exec: RegExpInstance -> string -> Result ExecResult _ :=
      @Frontend.regExpExec parameters.
    Definition search: RegExpInstance -> string -> Result.Result (integer * RegExpInstance) _ :=
      @Frontend.prototypeSearch parameters.
    Definition rmatch: RegExpInstance -> string -> Result.Result ProtoMatchResult _ :=
      @Frontend.prototypeMatch parameters.
    Definition test: RegExpInstance -> string -> Result.Result (bool * RegExpInstance) _ :=
      @Frontend.prototypeTest parameters.
  End Engine.

  (*  Other utils, such as functions of the specification which are not used in the mechanization, but could
      be useful to instantiate an engine from OCaml.
  *)
  Module Utils.
    Local Open Scope nat.
    Import Result.Notations.
    Local Open Scope result_flow.

    (* Required operations on utf16 strings. *)
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

      (** >> 
          11.1.4 Static Semantics: CodePointAt ( string, position )

          The abstract operation CodePointAt takes arguments string (a String) and position (a non-negative integer)
          and returns a Record with fields [[CodePoint]] (a code point), [[CodeUnitCount]] (a positive integer), and
          [[IsUnpairedSurrogate]] (a Boolean). It interprets string as a sequence of UTF-16 encoded code points, as
          described in 6.1.4, and reads from it a single code point starting with the code unit at index position.
          It performs the following steps when called:
      <<*)
      Definition codePointAt (string: Utf16String) (position: non_neg_integer): Result (non_neg_integer * bool) MatchError :=
        (*>> 1. Let size be the length of string. <<*)
        let size := length string in
        (*>> 2. Assert: position ≥ 0 and position < size. <<*)
        assert! (position >=? 0) && (position <? size) ;
        (*>> 3. Let first be the code unit at index position within string. <<*)
        let first := codeUnitAt string position in
        (*>> 4. Let cp be the code point whose numeric value is the numeric value of first. <<*)
        (*>> We don't return cp, so this isn't required <<*)
        (*>> 5. If first is neither a leading surrogate nor a trailing surrogate, then <<*)
        if negb (is_leading_surrogate first) && negb (is_trailing_surrogate first) then
          (*>> a. Return the Record { [[CodePoint]]: cp, [[CodeUnitCount]]: 1, [[IsUnpairedSurrogate]]: false }. <<*)
          Success (1, false)
        else
        (*>> 6. If first is a trailing surrogate or position + 1 = size, then <<*)
        if is_trailing_surrogate first || ((position + 1) == size) then
          (*>> a. Return the Record { [[CodePoint]]: cp, [[CodeUnitCount]]: 1, [[IsUnpairedSurrogate]]: true }. <<*)
          Success (1, true)
        else
        (*>> 7. Let second be the code unit at index position + 1 within string. <<*)
        let second := codeUnitAt string (position + 1) in
        (*>> 8. If second is not a trailing surrogate, then <<*)
        if negb (is_trailing_surrogate second) then
          (*>> a. Return the Record { [[CodePoint]]: cp, [[CodeUnitCount]]: 1, [[IsUnpairedSurrogate]]: true }. <<*)
          Success (1, true)
        else
        (*>> 9. Set cp to UTF16SurrogatePairToCodePoint(first, second). <<*)
        (*+ We don't return cp, so this isn't required +*)
        (*>> 10. Return the Record { [[CodePoint]]: cp, [[CodeUnitCount]]: 2, [[IsUnpairedSurrogate]]: false }. <<*)
        Success (2, false).


      (** >>
          22.2.7.3 AdvanceStringIndex ( S, index, unicode )

          The abstract operation AdvanceStringIndex takes arguments S (a String), index (a non-negative integer),
          and unicode (a Boolean) and returns an integer. It performs the following steps when called:
      <<*)
      (*+ This function is specialized to only handle the unicode case; the other case is uninteresting. +*)
      Definition advanceStringIndex (S: Utf16String) (index: non_neg_integer) : Result.Result non_neg_integer MatchError :=
        (*>> 1. Assert: index ≤ 2^53 - 1. <<*)
        (*+ We don't include numeric limits +*)
        (*>> If unicode is false, return index + 1. <<*)
        (*+ Unicode is always true +*)
        (*>> 3. Let length be the length of S. <<*)
        let length := length S in
        (*>> 4. If index + 1 ≥ length, return index + 1. <<*)
        if (index + 1) >=? length then Success (index + 1) else
        (*>> 5. Let cp be CodePointAt(S, index). <<*)
        let! (codeUnitCount, _) =<< codePointAt S index in
        (*>> 6. Return index + cp.[[CodeUnitCount]]. <<*)
        Success (index + codeUnitCount)%nat.

      (** >>
          22.2.7.4 GetStringIndex ( S, codePointIndex )

          The abstract operation GetStringIndex takes arguments S (a String) and codePointIndex (a non-negative integer)
          and returns a non-negative integer. It interprets S as a sequence of UTF-16 encoded code points, as described
          in 6.1.4, and returns the code unit index corresponding to code point index codePointIndex when such an index
          exists. Otherwise, it returns the length of S. It performs the following steps when called:
      <<*)
      Definition getStringIndex (S: Utf16String) (codePointIndex: non_neg_integer) : Result.Result non_neg_integer MatchError :=
        (*>> If S is the empty String, return 0. <<*)
        if length S == 0 then Success 0 else
        (*>> 2. Let len be the length of S. <<*)
        let len := length S in
        (*>> 3. Let codeUnitCount be 0. <<*)
        let codeUnitCount := 0 in
        (*>> 4. Let codePointCount be 0. <<*)
        let codePointCount := 0 in
        (*>> 5. Repeat, while codeUnitCount < len, <<*)
        let! res =<< Return.while MatchError.OutOfFuel (len + 2) (codeUnitCount, codePointCount)
          (fun p => let (codeUnitCount, _) := p in codeUnitCount <? len)
          (fun p => let (codeUnitCount, codePointCount) := p in
            (*>> a. If codePointCount = codePointIndex, return codeUnitCount. <<*)
            if codePointCount == codePointIndex then Success (Return.ret codeUnitCount) else
            (*>> b. Let cp be CodePointAt(S, codeUnitCount). <<*)
            let! (cp_codeUnitCount, _) =<< codePointAt S codeUnitCount in
            (*>> c. Set codeUnitCount to codeUnitCount + cp.[[CodeUnitCount]]. <<*)
            let codeUnitCount := codeUnitCount + cp_codeUnitCount in
            (*>> d. Set codePointCount to codePointCount + 1. <<*)
            let codePointCount := codePointCount + 1 in
            Success (Return.continue (codeUnitCount, codePointCount)))
        in
        match res with
        | Return.Returned v => Success v
        | Return.Continue (codeUnitCount, codePointCount) =>
            (*>> 6. Return len. <<*)
            Success codeUnitCount
        end.
    End UnicodeOps.
  End Utils.

End API.