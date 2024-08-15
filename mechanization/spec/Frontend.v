From Coq Require Import List ZArith.
From Warblre Require Import RegExpRecord Base Errors Notation Patterns Node StaticSemantics Semantics Result List Characters Return.

Import Result.Notations.
Import Notation.
Import Patterns.
Local Open Scope result_flow.
(** >>
  WILDCARD Sections
  ["22.2.3","22.2.3.1","22.2.3.2","22.2.3.4","22.2.4","22.2.4.1","22.2.5","22.2.5.1","22.2.5.2","22.2.6","22.2.6.1","22.2.6.2","22.2.6.3","22.2.6.4",
    "22.2.6.4.1","22.2.6.5","22.2.6.6","22.2.6.7","22.2.6.9","22.2.6.10","22.2.6.11","22.2.6.13","22.2.6.13.1","22.2.6.14","22.2.6.15","22.2.6.17",
    "22.2.6.18","22.2.7","22.2.7.2","22.2.7.8","22.2.9.2","22.2.9.2.1","22.2.9.2.2"]
<<*)
(**+
      This file doesn't follow the specification as closely as the other files.

      This part of the spec relies heavily on the semantics and execution model of JavaScript.
      As such, it is more difficult to follow it closely without having formalized many other aspects of language,
      which are typically irrelevant to the execution of regexes.

      Additionally, this section relies more heavily on imperative features than the other section.
+**)

(* + The flags are represented using a string in the spec. +*)
Module RegExpFlags.
  Record type := make {
    d: bool;
    g: bool;
    i: bool;
    m: bool;
    s: bool;
    u: unit;
    y: bool;
  }.
End RegExpFlags.
Notation RegExpFlags := RegExpFlags.type.
Notation reg_exp_flags := RegExpFlags.make.

(** >>
    22.2.8 Properties of RegExp Instances

    RegExp instances are ordinary objects that inherit properties from the RegExp prototype object.
    RegExp instances have internal slots [[OriginalSource]], [[OriginalFlags]], [[RegExpRecord]], and [[RegExpMatcher]].
    The value of the [[RegExpMatcher]] internal slot is an Abstract Closure representation of the Pattern of the
    RegExp object.

    RegExp instances also have the following property:
      22.2.8.1 lastIndex
      The value of the "lastIndex" property specifies the String index at which to start the next match.
      It is coerced to an integral Number when used (see 22.2.7.2).
      This property shall have the attributes { [[Writable]]: true, [[Enumerable]]: false, [[Configurable]]: false }.
      22.2.9 RegExp String Iterator Objects
      A RegExp String Iterator is an object, that represents a specific iteration over some specific String instance
      object, matching against some specific RegExp instance object. There is not a named constructor for RegExp String
      Iterator objects. Instead, RegExp String Iterator objects are created by calling certain methods of RegExp
      instance objects.
<<*)
Module RegExpInstance. Section main.
  Local Definition String {T: Type} `{StringMarker T} := T.
  Local Definition Character {T: Type} `{CharacterMarker T} := T.
  Local Definition UnicodeProperty {T: Type} `{UnicodePropertyMarker T} := T.
  Context {Character_ String_ UnicodeProperty_: Type}
    `{CharacterMarker Character_} `{StringMarker String_} `{UnicodePropertyMarker UnicodeProperty_}.

  Record type := make {
      originalSource: Patterns.Regex;
      originalFlags: RegExpFlags;
      regExpRecord: RegExpRecord;
      regExpMatcher: list Character -> non_neg_integer -> MatchResult;
      lastIndex: integer;
    }.

  Definition setLastIndex (r: type) (index: integer): type :=
    make (originalSource r) (originalFlags r) (regExpRecord r) (regExpMatcher r) index.
End main. End RegExpInstance.
Notation RegExpInstance := RegExpInstance.type.
Notation reg_exp_instance := RegExpInstance.make.

Section Initialization.
  Context `{specParameters: Parameters}.

  (** >>
      22.2.3.3 RegExpInitialize ( obj, pattern, flags )

      The abstract operation RegExpInitialize takes arguments obj (an Object), pattern (an ECMAScript language value),
      and flags (an ECMAScript language value) and returns either a normal completion containing an Object or a throw
      completion. It performs the following steps when called:
  <<*)
  Definition regExpInitialize (pattern: Regex) (flags: RegExpFlags) : Result RegExpInstance CompileError :=
    (*>> 1. If pattern is undefined, let P be the empty String. <<*)
    (*>> 2. Else, let P be ? ToString(pattern). <<*)
    let P := pattern in

    (*>> 3. If flags is undefined, let F be the empty String. <<*)
    (*>> 4. Else, let F be ? ToString(flags). <<*)
    let F := flags in
    (*>> 5. If F contains any code unit other than "d", "g", "i", "m", "s", "u", or "y", or if F contains any code unit more than once, throw a SyntaxError exception. <<*)
    (* + Ensured by F's type. +*)

    (*>> 6. If F contains "i", let i be true; else let i be false. <<*)
    let i := RegExpFlags.i F in
    (*>> 7. If F contains "m", let m be true; else let m be false. <<*)
    let m := RegExpFlags.m F in
    (*>> 8. If F contains "s", let s be true; else let s be false. <<*)
    let s := RegExpFlags.s F in
    (*>> 9. If F contains "u", let u be true; else let u be false. <<*)
    let u := RegExpFlags.u F in

    (*>> 10. If u is true, then <<*)
      (*>> a. Let patternText be StringToCodePoints(P). <<*)
    (*>> 11. Else, <<*)
      (*>> a. Let patternText be the result of interpreting each of P's 16-bit elements as a Unicode BMP code point. UTF-16 decoding is not applied to the elements. <<*)
    (*>> 12. Let parseResult be ParsePattern(patternText, u). <<*)
    (* + We don't include parsing, to this step was already done. +*)
    (*>> 13. If parseResult is a non-empty List of SyntaxError objects, throw a SyntaxError exception. <<*)
    (*>> 14. Assert: parseResult is a Pattern Parse Node. <<*)
    let patternText := P in
    let parseResult := patternText in

    (*>> 15. Set obj.[[OriginalSource]] to P. <<*)
    let obj_originalSource := P in
    (*>> 16. Set obj.[[OriginalFlags]] to F. <<*)
    let obj_originalFlags := F in
    (*>> 17. Let capturingGroupsCount be CountLeftCapturingParensWithin(parseResult). <<*)
    let capturingGroupsCount := countLeftCapturingParensWithin pattern nil in
    (*>> 18. Let rer be the RegExp Record { [[IgnoreCase]]: i, [[Multiline]]: m, [[DotAll]]: s, [[Unicode]]: u, [[CapturingGroupsCount]]: capturingGroupsCount }. <<*)
    let rer := reg_exp_record i m s u capturingGroupsCount in
    (*>> 19. Set obj.[[RegExpRecord]] to rer. <<*)
    let obj_RegExpRecord := rer in
    (*>> 20. Set obj.[[RegExpMatcher]] to CompilePattern of parseResult with argument rer. <<*)
    let! obj_RegExpMatcher =<< Semantics.compilePattern parseResult rer in
    (*>> 21. Perform ? Set(obj, "lastIndex", +0𝔽, true). <<*)
    let obj_lastIndex := 0%Z in
    (*>> 22. Return obj. <<*)
    Success (reg_exp_instance obj_originalSource obj_originalFlags obj_RegExpRecord obj_RegExpMatcher obj_lastIndex).
End Initialization.

(** >>
    22.2.7.5 Match Records

    A Match Record is a Record value used to encapsulate the start and end indices of a regular expression match or capture.
    Match Records have the fields listed in Table 67.
<<*)
Module MatchRecord.
  Record type := mk {
    (* + [[StartIndex]] 	a non-negative integer + *)
    startIndex: non_neg_integer;
    (* + [[EndIndex]] 	an integer ≥ [[StartIndex]] + *)
    endIndex: non_neg_integer;
  }.

  (* + The specification mentions that endIndex >= startIndex. We encode this restriction using a runtime check in this alternative constructor. +*)
  Definition make (mstart: non_neg_integer) (mend: non_neg_integer) : Result.Result type MatchError :=
    assert! (mend >=? mstart);
    Success (mk mstart mend).
End MatchRecord.
Notation MatchRecord := MatchRecord.type.
Notation match_record := MatchRecord.make.

(* + the groups that are returned inside the obejct returned by RegExpBuiltinExec +*)
Definition groups_map {S} `{StringMarker S}: Type := list (GroupName * option S).

  (* +
      RegExpBuiltinExec returns an array exotic, i.e. a blob mapping names and indices to (JS) values.
      We instead use, and define here, a statically typed record to represent these returned values.
  +*)
Module ExecArrayExotic. Section main.
  Local Definition String {T: Type} `{StringMarker T} := T.
  Local Definition Character {T: Type} `{CharacterMarker T} := T.
  Context {Character_ String_: Type} `{CharacterMarker Character_} `{StringMarker String_}.

  Record type := make {
      index: nat;
      input: String;
      array: list (option String); 
      groups: option groups_map;
      indices_array: option (list (option (nat * nat)));
      indices_groups: option (list (GroupName * option (nat * nat)));
    }.
End main. End ExecArrayExotic.
Notation ExecArrayExotic := ExecArrayExotic.type.
Notation exec_array_exotic := ExecArrayExotic.make.

Inductive ExecResult {C S UP: Type} `{CharacterMarker C} `{StringMarker S} `{UnicodePropertyMarker UP} :=
| Null: RegExpInstance -> ExecResult (* + also returns modifications to the RegExpInstance Object +*)
| Exotic: ExecArrayExotic -> RegExpInstance -> ExecResult.

Inductive ProtoMatchResult {C S UP: Type} `{CharacterMarker C} `{StringMarker S} `{UnicodePropertyMarker UP}  :=
| GlobalResult : option (list S) -> RegExpInstance -> ProtoMatchResult 
| NonGlobalResult : ExecResult -> ProtoMatchResult.

Section BuiltinExec.
  Context `{specParameters: Parameters}.

  (** >>
      22.2.7.7 GetMatchIndexPair ( S, match )

      The abstract operation GetMatchIndexPair takes arguments S (a String) and match (a Match Record) and returns an
      Array. It performs the following steps when called:
  <<*)

  Definition getMatchIndexPair (S: String) (match_rec: MatchRecord) : Result.Result (nat * nat) MatchError :=
    (*>> 1. Assert: match.[[StartIndex]] ≤ match.[[EndIndex]] ≤ the length of S. <<*)
    assert! ((MatchRecord.startIndex match_rec) <=? (MatchRecord.endIndex match_rec));
    assert! ((MatchRecord.endIndex match_rec) <=? String.length S);
    (*>> 2. Return CreateArrayFromList(« 𝔽(match.[[StartIndex]]), 𝔽(match.[[EndIndex]]) »). <<*)
    Success (MatchRecord.startIndex match_rec, MatchRecord.endIndex match_rec).

  (** >>
      22.2.7.8 MakeMatchIndicesIndexPairArray ( S, indices, groupNames, hasGroups )

      The abstract operation MakeMatchIndicesIndexPairArray takes arguments S (a String), indices
      (a List of either Match Records or undefined), groupNames (a List of either Strings or undefined),
      and hasGroups (a Boolean) and returns an Array. It performs the following steps when called:
  <<*)
  (* + NOTE: we separate this in two functions: one computing the indices array, the other one computing the groups +*)
  (* + NOTE: here hasGroups means "has **named** groups" +*)

  Fixpoint makeMatchIndicesArray (S: String) (indices: list (option MatchRecord)): Result.Result (list (option (nat*nat))) MatchError :=
    match indices with
    | nil => Success nil
    (*>> a. Let matchIndices be indices[i]. <<*)
    | matchIndices::indices' =>
        let! matchIndexPair =<<
             match matchIndices with
             (*>> b. If matchIndices is not undefined, then <<*)
             | Some match_rec =>
                 (*>> i. Let matchIndexPair be GetMatchIndexPair(S, matchIndices). <<*)
                 let! mpair =<< getMatchIndexPair S match_rec in
                 Success (Some mpair)
             (*>> c. Else, <<*)
             (*>> i. Let matchIndexPair be undefined <<*)
             | None => Success None
             end in
        let! next =<< makeMatchIndicesArray S indices' in
        (*>> d. Perform ! CreateDataPropertyOrThrow(A, ! ToString(𝔽(i)), matchIndexPair). <<*)
        Success (matchIndexPair :: next)
    end.


  (* + assuming that indices does not contain the first element +*)
  Fixpoint makeMatchIndicesGroupList (S: String) (indices: list (option MatchRecord)) (groupNames:list (option GroupName)): Result.Result (list (GroupName * option (nat*nat))) MatchError :=
     match indices with
    | nil => Success nil
    (*>> a. Let matchIndices be indices[i]. <<*)
    | matchIndices::indices' =>
        let! matchIndexPair =<<
             match matchIndices with
             (*>> b. If matchIndices is not undefined, then <<*)
             | Some match_rec =>
                 (*>> i. Let matchIndexPair be GetMatchIndexPair(S, matchIndices). <<*)
                 let! mpair =<< getMatchIndexPair S match_rec in
                 Success (Some mpair)
             (*>> c. Else, <<*)
             (*>> i. Let matchIndexPair be undefined <<*)
             | None => Success None
             end in
        match groupNames with
        | nil => Error MatchError.AssertionFailed
        | gn::groupNames' =>
            let! next =<< makeMatchIndicesGroupList S indices' groupNames' in
            match gn with
            | None => Success next
            (*>> e. If i > 0 and groupNames[i - 1] is not undefined, then <<*)
            (*>> ii. Perform ! CreateDataPropertyOrThrow(groups, groupNames[i - 1], matchIndexPair). <<*)
            | Some name => Success ((name,matchIndexPair)::next)
            end
        end
     end.

  Definition MakeMatchIndicesGroups (S: String) (indices:list (option MatchRecord)) (groupNames:list (option GroupName)) (hasGroups:bool): Result.Result (option (list (GroupName * option (nat*nat)))) MatchError :=
    (*>> 1. Let n be the number of elements in indices. <<*)
    let n := List.length indices in
    (*>> [OMITTED] 2. Assert: n < 2^32 - 1. <<*)
    (* + assert! (n <? 4294967295)%nat; +*)
    (*>> 3. Assert: groupNames has n - 1 elements. <<*)
    assert! (Nat.eqb (List.length groupNames) (n-1));
      match hasGroups with
      | false => Success None
      | true => 
          match indices with
          | indices_zero::indices' =>
              let! groups =<< makeMatchIndicesGroupList S indices' groupNames in
              Success (Some groups)
          | nil => Error MatchError.AssertionFailed
          end
      end.

  (** >>
      22.2.7.6 GetMatchString ( S, match )

      The abstract operation GetMatchString takes arguments S (a String) and match (a Match Record) and returns a
      String. It performs the following steps when called:
  <<*)
  Definition getMatchString (S: String) (matsh: MatchRecord) : Result.Result String MatchError :=
    (*>> 1. Assert: match.[[StartIndex]] ≤ match.[[EndIndex]] ≤ the length of S. <<*)
    assert! ((MatchRecord.startIndex matsh) <=? (MatchRecord.endIndex matsh));
    assert! ((MatchRecord.endIndex matsh) <=? String.length S);
    (*>> 2. Return the substring of S from match.[[StartIndex]] to match.[[EndIndex]]. <<*)
    Success (String.substring S (MatchRecord.startIndex matsh) (MatchRecord.endIndex matsh)).

  (** >>
      22.2.7.2 RegExpBuiltinExec ( R, S )

      The abstract operation RegExpBuiltinExec takes arguments R (an initialized RegExp instance) and S (a String) and
      returns either a normal completion containing either an Array exotic object or null, or a throw completion.
      It performs the following steps when called:
  <<*)

  (* + The inner repeat loop can either make the whole function terminate +*)
  (* + Or it lets the whole function go on, but defines (r:MatchState) and (lastIndex:nat) +*)
  Inductive LoopResult :=
  | Terminates: ExecResult -> LoopResult
  | Continues: MatchState -> nat -> LoopResult.

  (* + transforms a capture into a capturedValue, a substring of the original string +*)
  Definition capture_to_value (S: String) (cI:option CaptureRange) : Result.Result (option (String)) MatchError :=
    match cI with
    (* b. If captureI is undefined, then
    i. Let capturedValue be undefined. *)
    | None => Success None
    (*>> c. Else, <<*)
    | Some captureI =>
        (*>> i. Let captureStart be captureI.[[StartIndex]]. <<*)
        let! captureStart =<< NonNegInt.from_int (CaptureRange.startIndex captureI) in
        (*>> ii. Let captureEnd be captureI.[[EndIndex]]. <<*)
        let! captureEnd =<< NonNegInt.from_int (CaptureRange.endIndex captureI) in
        (*>> iii. If fullUnicode is true, then <<*)
           (*>> 1. Set captureStart to GetStringIndex(S, captureStart). <<*)
        let captureStart := String.getStringIndex S captureStart in
           (*>> 2. Set captureEnd to GetStringIndex(S, captureEnd). <<*)
        let captureEnd := String.getStringIndex S captureEnd in
        (*>> iv. Let capture be the Match Record { [[StartIndex]]: captureStart, [[EndIndex]]: captureEnd }. <<*)
        let! capture =<< match_record captureStart captureEnd in
        (*>> v. Let capturedValue be GetMatchString(S, capture). <<*)
        let! capturedValue =<< getMatchString S capture in
        Success (Some capturedValue)
    end.

  (* + computes the array part of the Exotic Array, but only for captures with an index >= 1 +*)
  Fixpoint captures_to_array (S: String) (captures: list (option CaptureRange)) : Result.Result (list (option (String))) MatchError :=
    (*>> 33. For each integer i such that 1 ≤ i ≤ n, in ascending order, do <<*)
    match captures with
    | nil => Success nil
    (*>> a. Let captureI be ith element of r's captures List. <<*)
    | captureI::captures' =>
        let! capturedValue =<< capture_to_value S captureI in
        let! next =<< captures_to_array S captures' in
        (*>> d. Perform ! CreateDataPropertyOrThrow(A, ! ToString(𝔽(i)), capturedValue). <<*)
        Success (capturedValue::next)
    end.

  (* + i is the index of the first group in the captures list (initially, 1) +*)
  Fixpoint captures_to_groupsmap (R: Regex) (S: String) (captures: list (option CaptureRange)) (i: non_neg_integer): Result.Result groups_map MatchError :=
    match captures with
    | nil => Success nil
    | captureI::captures' =>
        let! capturedValue =<< capture_to_value S captureI in
        let! node =<< nth_group R i in
        destruct! (Group groupname _, _) <- node in
        let! next =<< captures_to_groupsmap R S captures' (i+1) in
        (*>> e. If the ith capture of R was defined with a GroupName, then <<*)
        match groupname with
        | None => Success next
        (*>> i. Let s be the CapturingGroupName of that GroupName. <<*)
        (*>> ii. Perform ! CreateDataPropertyOrThrow(groups, s, capturedValue). <<*)
        | Some s => Success ((s,capturedValue) :: next)
        end
    end.

  (* + computes the groups map, associating each group name to its captured value +*)
  Definition captures_to_groups_map (R:Regex) (S: String) (captures: list (option CaptureRange)) : Result.Result groups_map MatchError :=
    captures_to_groupsmap R S captures 1%nat.

  Fixpoint captures_to_groupnames (R:Regex) (captures:list (option CaptureRange)) (i:nat): Result.Result (list (option GroupName)) MatchError :=
    match captures with
    | nil => Success nil
    | captureI::captures' =>
        let! node =<< nth_group R i in
        destruct! (Group groupname _, _) <- node in
        let! next =<< captures_to_groupnames R captures' (i+1) in
        match groupname with
        (*>> iii. Append s to groupNames. <<*)
        | Some s => Success ((Some s)::next)
        (*>> f. Else, <<*)
        (*>> i. Append undefined to groupNames. <<*)
        | None => Success (None::next)
        end
    end.

  Definition captures_to_group_names (R:Regex)  (captures:list (option CaptureRange)): Result.Result (list (option GroupName)) MatchError :=
    captures_to_groupnames R captures 1%nat.

  (* + transforms a capture into a matchRecord +*)
  Definition capture_to_record (S: String) (cI: option CaptureRange) : Result.Result (option MatchRecord) MatchError :=
    match cI with
    (* b. If captureI is undefined, then
    i. Let capturedValue be undefined. *)
    | None => Success None
    (*>> c. Else, <<*)
    | Some captureI =>
        (*>> i. Let captureStart be captureI.[[StartIndex]]. <<*)
        let! captureStart =<< NonNegInt.from_int (CaptureRange.startIndex captureI) in
        (*>> ii. Let captureEnd be captureI.[[EndIndex]]. <<*)
        let! captureEnd =<< NonNegInt.from_int (CaptureRange.endIndex captureI) in
        (*>> iii. If fullUnicode is true, then <<*)
           (*>> 1. Set captureStart to GetStringIndex(S, captureStart). <<*)
        let captureStart := String.getStringIndex S captureStart in
           (*>> 2. Set captureEnd to GetStringIndex(S, captureEnd). <<*)
        let captureEnd := String.getStringIndex S captureEnd in
        (*>> iv. Let capture be the Match Record { [[StartIndex]]: captureStart, [[EndIndex]]: captureEnd }. <<*)
        let! capture =<< match_record captureStart captureEnd in
        (*>> vi. Append capture to indices. <<*)
        Success (Some capture)
    end.

  (* + computes the indices list +*)
  Fixpoint captures_to_indices (S: String) (captures:list (option CaptureRange)) : Result.Result (list (option MatchRecord)) MatchError :=
    (*>> 33. For each integer i such that 1 ≤ i ≤ n, in ascending order, do <<*)
    match captures with
    | nil => Success nil
    (*>> a. Let captureI be ith element of r's captures List. <<*)
    | captureI :: captures' =>
        let! record =<< capture_to_record S captureI in
        let! next =<< captures_to_indices S captures' in
        Success (record :: next)
    end.

  (* + Map an index in the original (i.e UTF16) string into the char list +*)
  Definition to_list_index (stringIndex: nat) (S: String): Result.Result nat MatchError :=
    let fix iter (count: nat) (current: nat): Result.Result nat MatchError :=
      if (current == stringIndex)%nat then Success (stringIndex - count)%nat
      else
      match count with
      | 0 => out_of_fuel
      | S count' => iter count' (String.advanceStringIndex S current)
      end
    in
    iter stringIndex 0.

  Definition regExpBuiltinExec (R: RegExpInstance) (S: String): Result.Result ExecResult MatchError :=
    (*>> 1. Let length be the length of S. <<*)
    let length := String.length S in
    (*>> 2. Let lastIndex be ℝ(? ToLength(? Get(R, "lastIndex"))). <<*)
    let lastIndex := RegExpInstance.lastIndex R in
    (*>> 3. Let flags be R.[[OriginalFlags]]. <<*)
    let flags := RegExpInstance.originalFlags R in
    (*>> 4. If flags contains "g", let global be true; else let global be false. <<*)
    let global := RegExpFlags.g flags in
    (*>> 5. If flags contains "y", let sticky be true; else let sticky be false. <<*)
    let sticky := RegExpFlags.y flags in
    (*>> 6. If flags contains "d", let hasIndices be true; else let hasIndices be false. <<*)
    let hasIndices := RegExpFlags.d flags in
    (*>> 7. If global is false and sticky is false, set lastIndex to 0. <<*)
    let lIndex: integer := if (andb (negb global) (negb sticky)) then 0%Z else lastIndex in
    let! lastIndex: non_neg_integer =<< NonNegInt.from_int lIndex in
    (*>> 8. Let matcher be R.[[RegExpMatcher]]. <<*)
    let matcher := RegExpInstance.regExpMatcher R in
    (*>> 9. If flags contains "u", let fullUnicode be true; else let fullUnicode be false. <<*)
    let fullUnicode := RegExpFlags.u in
    (*>> 10. Let matchSucceeded be false. <<*)
    let matchSucceeded := false in
    (*>> 11. If fullUnicode is true, let input be StringToCodePoints(S). Otherwise, let input be a List whose elements are the code units that are the elements of S. <<*)
    let input := String.to_char_list S in
    (*>> 12. NOTE: Each element of input is considered to be a character. <<*)
    (*>> 13. Repeat, while matchSucceeded is false, <<*)
    (* + We change the repeat loop to a recursive function with fuel +*)
    let fix repeatloop (lastIndex: nat) (fuel: nat): Result LoopResult MatchError :=
      match fuel with
      | 0 => out_of_fuel
      | S fuel' =>
          (*>> a. If lastIndex > length, then <<*)
          if (lastIndex >? length)%nat then
            (*>> i. If global is true or sticky is true, then <<*)
            let R := if (orb global sticky) then
                       (*>> 1. Perform ? Set(R, "lastIndex", +0𝔽, true). <<*)
                       RegExpInstance.setLastIndex R 0%Z
                     else R in
            (*>> ii. Return null. <<*)
            Success (Terminates (Null R))
          else
          (*>> b. Let inputIndex be the index into input of the character that was obtained from element lastIndex of S. <<*)
          (* + Nasty piece of english prose... +*)
          let! inputIndex =<< to_list_index lastIndex S in
          (*>> c. Let r be matcher(input, inputIndex). <<*)
          let! r:(option MatchState) =<< matcher input inputIndex in
          (*>> d. If r is failure, then <<*)
          (* + LATER: change once fix is released +*)
          (* + The more natural looking r == failure
              Triggers https://github.com/coq/coq/issues/18358 with coq < 8.20 *)
          if @EqDec.eq_dec _ eqdec_option r failure then
            (*>> i. If sticky is true, then <<*)
            if sticky then
              (*>> 1. Perform ? Set(R, "lastIndex", +0𝔽, true). <<*)
              let R := RegExpInstance.setLastIndex R 0%Z in
              (*>> 2. Return null. <<*)
              Success (Terminates (Null R))
            else
            (*>> ii. Set lastIndex to AdvanceStringIndex(S, lastIndex, fullUnicode). <<*)
            let lastIndex := @String.advanceStringIndex _ string_string S lastIndex in
            repeatloop lastIndex fuel'
          (*>> e. Else <<*)
          else
            (*>> i. Assert: r is a MatchState. <<*)
            assert! (r is (Some _));
            destruct! Some r <- (r:option MatchState) in
            (*>> ii. Set matchSucceeded to true. <<*)
            Success (Continues r lastIndex)
    end in
    (* + we know that there are at most length+1 iterations, we can use that as fuel +*)
    let! repeatresult =<< repeatloop lastIndex ((List.length input) +2) in
    match repeatresult with
    | Terminates execresult => Success (execresult)
    | Continues r lastIndex =>
        (*>> 14. Let e be r.[[EndIndex]]. <<*)
        (* + Missing integer conversion +*)
        let! e: non_neg_integer =<< NonNegInt.from_int (MatchState.endIndex r) in
        (*>> 15. If fullUnicode is true, set e to GetStringIndex(S, e). <<*)
        let e := String.getStringIndex S e in
        (*>> 16. If global is true or sticky is true, then <<*)
        let R := if (orb global sticky) then
                             (*>> a. Perform ? Set(R, "lastIndex", 𝔽(e), true). <<*)
                             RegExpInstance.setLastIndex R (NonNegInt.to_int e)
                           else R in
        (*>> 17. Let n be the number of elements in r.[[Captures]]. <<*)
        let n := List.length (MatchState.captures r) in
        (*>> 18. Assert: n = R.[[RegExpRecord]].[[CapturingGroupsCount]]. <<*)
        assert! (Nat.eqb (n) (RegExpRecord.capturingGroupsCount (RegExpInstance.regExpRecord R)));
        (*>> [OMITTED] 19. Assert: n < 2^32 - 1. <<*)
        (* + assert! (n <? 4294967295)%nat; +*)
        (*>> 20. Let A be ! ArrayCreate(n + 1). <<*)
        (*>> 22. Perform ! CreateDataPropertyOrThrow(A, "index", 𝔽(lastIndex)). <<*)
        let A_index := lastIndex in
        (*>> 23. Perform ! CreateDataPropertyOrThrow(A, "input", S). <<*)
        let A_input := S in
        (*>> 24. Let match be the Match Record { [[StartIndex]]: lastIndex, [[EndIndex]]: e }. <<*)
        let! match_rec =<< match_record lastIndex e in
        (*>> 28. Let matchedSubstr be GetMatchString(S, match). <<*)
        let! matchedSubstr =<< getMatchString S match_rec in
        (*>> 29. Perform ! CreateDataPropertyOrThrow(A, "0", matchedSubstr). <<*)
        let A_array_zero := Some matchedSubstr in
        let! A_array_next =<< captures_to_array S (MatchState.captures r) in
        let A_array := A_array_zero :: A_array_next in
        (*>> 21. Assert: The mathematical value of A's "length" property is n + 1. <<*)
        assert! (Nat.eqb (List.length A_array) (n+1));
        (*>> 30. If R contains any GroupName, then <<*)
        let hasGroups := StaticSemantics.defines_groups (RegExpInstance.originalSource R) in
        let! A_groups =<< if hasGroups then 
          let! groupsmap =<< captures_to_groups_map (RegExpInstance.originalSource R) S (MatchState.captures r) in
          Success (Some groupsmap)
        (*>> 31. Else, <<*)
        else
          (*>> a. Let groups be undefined. <<*)
          Success None
        in
        (*>> 27. Append match to indices. <<*)
        let! indices_next =<< captures_to_indices S (MatchState.captures r) in
        let indices := (Some match_rec) :: indices_next in
        let! groupNames =<< captures_to_group_names (RegExpInstance.originalSource R) (MatchState.captures r) in
        (*>> 34. a. Let indicesArray be MakeMatchIndicesIndexPairArray(S, indices, groupNames, hasGroups). <<*)
        let! A_indices_array =<<
             if hasIndices then
               let! array =<< makeMatchIndicesArray S indices in
               Success (Some array)
             else Success None in
        let! A_indices_groups =<<
             if hasIndices then MakeMatchIndicesGroups S indices groupNames hasGroups
             else Success None in
        Success (Exotic (exec_array_exotic A_index A_input A_array A_groups A_indices_array A_indices_groups) (R))
  end.
End BuiltinExec.

Section API.
  Context `{specParameters: Parameters}.

  (** >>
      22.2.7.1 RegExpExec ( R, S )

      The abstract operation RegExpExec takes arguments R (an Object) and S (a String) and returns either a normal
      completion containing either an Object or null, or a throw completion. It performs the following steps when called:
  <<*)
  Definition regExpExec (R: RegExpInstance) (S: String): Result.Result ExecResult MatchError :=
    (*>> [OMITTED] 1. Let exec be ? Get(R, "exec").
         2.IfIsCallable(exec) istrue, then
           a. Let result be ? Call(exec, R, « S »).
           b. If result is not an Object and result is not null, throw a TypeError exception.
           c. Return result.
         3. Perform ? RequireInternalSlot(R, [[RegExpMatcher]]). <<*)
    (*>> 4. Return ? RegExpBuiltinExec(R, S). <<*)
    regExpBuiltinExec R S.

  (** >>
      22.2.6.8 RegExp.prototype [ @@match ] ( string )

      This method performs the following steps when called:
  <<*)
  Definition get_head {A:Type} (l:list A) : Result A MatchError :=
    match l with
    | nil => Result.assertion_failed
    | a :: _ => Success a
    end.


  Definition prototypeMatch (R: RegExpInstance) (S: String): Result.Result ProtoMatchResult MatchError :=
    (*>> 1. Let rx be the this value. <<*)
    let rx := R in
    (*>> 2. If rx is not an Object, throw a TypeError exception. <<*)
    (*>> 3. Let S be ? ToString(string). <<*)
    let S := S in
    (*>> 4. Let flags be ? ToString(? Get(rx, "flags")). <<*)
    let flags := RegExpInstance.originalFlags rx in
    match (RegExpFlags.g flags) with
    (*>> 5. If flags does not contain "g", then <<*)
    | false =>
        (*>> a. Return ? RegExpExec(rx, S). <<*)
        let! exec_res =<< regExpExec rx S in
        Success (NonGlobalResult exec_res)
    (*>> 6. Else, <<*)
    | true =>
        (*>> a. If flags contains "u", let fullUnicode be true. Otherwise, let fullUnicode be false. <<*)
        let fullUnicode := RegExpFlags.u flags in
        (*>> b. Perform ? Set(rx, "lastIndex", +0𝔽, true). <<*)
        let rx := RegExpInstance.setLastIndex rx 0%Z in
        (*>> c. Let A be ! ArrayCreate(0). <<*)
        let A := nil in
        (*>> d. Let n be 0. <<*)
        let n := 0 in
        (*>> e. Repeat, <<*)
        let fix repeatloop (A: list (String)) (rx: RegExpInstance) (fuel: nat) (n: nat): Result.Result (option (list (String)) * RegExpInstance) MatchError :=
          match fuel with
          | O => out_of_fuel
          | S fuel' =>
              (*>> i. Let result be ? RegExpExec(rx, S). <<*)
              let! result =<< regExpExec rx S in
              match result with
              (*>> ii. If result is null, then <<*)
              | Null rx =>
                  (*>> 1. If n = 0, return null. <<*)
                  if (Nat.eqb n O)%nat then Success (None, rx)
                  (*>> 2. Return A. <<*)
                  else Success (Some A, rx)
              (*>> iii. Else, <<*)
              | Exotic result rx =>
                  (*>> 1. Let matchStr be ? ToString(? Get(result, "0")). <<*)
                  let! matchStrop =<< get_head (ExecArrayExotic.array result) in
                  let! matchStr =<< match matchStrop with | None => Error MatchError.AssertionFailed | Some s => Success s end in
                  (*>> 2. Perform ! CreateDataPropertyOrThrow(A, ! ToString(𝔽(n)), matchStr). <<*)
                  let A := app A (matchStr :: nil) in
                  (*>> 3. If matchStr is the empty String, then <<*)
                  let! rx =<< if (String.length matchStr == 0) then
                         (*>> a. Let thisIndex be ℝ(? ToLength(? Get(rx, "lastIndex"))). <<*)
                         let thisIndex := RegExpInstance.lastIndex rx in
                         let! thisIndexnat =<< NonNegInt.of_int thisIndex in
                         (*>> b. Let nextIndex be AdvanceStringIndex(S, thisIndex, fullUnicode). <<*)
                         let nextIndex := String.advanceStringIndex S thisIndexnat in
                         (*>> c. Perform ? Set(rx, "lastIndex", 𝔽(nextIndex), true). <<*)
                         Success (RegExpInstance.setLastIndex rx (BinInt.Z.of_nat nextIndex))
                       else Success rx in
                  (*>> 4. Set n to n + 1. <<*)
                  let n:= n + 1 in
                  repeatloop A rx fuel' n 
              end
          end in
        (* we know there are at most length S + 1 iterations since the index strictly increases *)
        let! (repeat_result, rx) =<< repeatloop A rx ((String.length S) +2) n in
        Success (GlobalResult repeat_result rx)
    end.

  (** >>
      22.2.6.12 RegExp.prototype [ @@search ] ( string )

      This method performs the following steps when called:
  <<*)
  Definition prototypeSearch (R: RegExpInstance) (S: String) : Result.Result (integer * RegExpInstance) MatchError :=
    (* + NOTE: The "lastIndex" and "global" properties of this RegExpRecord object are ignored when performing the search. The "lastIndex" property is left unchanged. +*)
    (*>> 1. Let rx be the this value. <<*)
    let rx := R in
    (*>> 2. If rx is not an Object, throw a TypeError exception. <<*)
    (*>> 3. Let S be ? ToString(string). <<*)
    (*>> 4. Let previousLastIndex be ? Get(rx, "lastIndex"). <<*)
    let previousLastIndex := RegExpInstance.lastIndex rx in
    (*>> 5. If SameValue(previousLastIndex, +0𝔽) is false, then <<*)
    let rx :=
      if (BinInt.Z.eqb previousLastIndex 0%Z) == false
        (*>> a. Perform ? Set(rx, "lastIndex", +0𝔽, true). <<*)
        then RegExpInstance.setLastIndex rx 0%Z
        else rx
    in
    (*>> 6. Let result be ? RegExpExec(rx, S). <<*)
    let! result =<< regExpExec rx S in
    (* + Emulate rx's mutation during exec +*)
    let rx := match result with | Null x => x | Exotic _ x => x end in
    (*>> 7. Let currentLastIndex be ? Get(rx, "lastIndex"). <<*)
    (* + Add conversion +*)
    let! currentLastIndex =<< NonNegInt.of_int (RegExpInstance.lastIndex rx) in
    (*>> 8. If SameValue(currentLastIndex, previousLastIndex) is false, then <<*)
    let rx :=
      if (BinInt.Z.eqb (NonNegInt.to_int currentLastIndex) previousLastIndex) == false
        (*>> a. Perform ? Set(rx, "lastIndex", previousLastIndex, true). <<*)
        then RegExpInstance.setLastIndex rx previousLastIndex
        else rx
    in
    match result with
    | Null _ =>
        (*>> 9. If result is null, return -1𝔽. <<*)
        Success ((-1)%Z, rx)
    | Exotic ArrayEx _ =>
        (*>> 10. Return ? Get(result, "index"). <<*)
        Success (BinInt.Z.of_nat (ExecArrayExotic.index ArrayEx), rx)
    end.


  (** >>
      22.2.6.16 RegExp.prototype.test ( S )

      This method performs the following steps when called:
  <<*)
  Definition prototypeTest (R: RegExpInstance) (S: String): Result.Result (bool * RegExpInstance) MatchError :=
    (*>> 1. Let R be the this value. <<*)
    let R := R in
    (*>> 2. If R is not an Object, throw a TypeError exception. <<*)
    (*>> 3. Let string be ? ToString(S). <<*)
    let string := S in
    (*>> 4. Let match be ? RegExpExec(R, string). <<*)
    let! match_res =<< regExpExec R string in
    (*>> 5. If match is not null, return true; else return false. <<*)
    match match_res with
    | Exotic A rx => Success (true, rx)
    | Null rx => Success (false, rx)
    end.

  (** >>
      22.2.9.1 CreateRegExpStringIterator ( R, S, global, fullUnicode )

      The abstract operation CreateRegExpStringIterator takes arguments R (an Object), S (a String), global (a Boolean),
      and fullUnicode (a Boolean) and returns a Generator. It performs the following steps when called:
  <<*)
  Definition createRegExpStringIterator (R: RegExpInstance) (S: String) (global: bool): Result.Result (list ExecArrayExotic * RegExpInstance) MatchError :=
    (*>> 1. Let closure be a new Abstract Closure with no parameters that captures R, S, global, and fullUnicode and performs the following steps when called: <<*)
    (*>> a. Repeat, <<*)
    let closure (R:RegExpInstance): Result.Result (option ExecArrayExotic * RegExpInstance) MatchError :=
      (*>> i. Let match be ? RegExpExec(R, S). <<*)
      let! match_result =<< regExpExec R S in
      match match_result with
        (*>> ii. If match is null, return undefined. <<*)
      | Null rx => Success (None, rx)
      | Exotic match_result rx =>
          (*>> iii. If global is false, then <<*)
          match global with
          | false =>
              (*>> 1. Perform ? GeneratorYield(CreateIterResultObject(match, false)). <<*)
              (*>> 2. Return undefined. <<*)
              Success (None, rx)
          | true =>
              (*>> iv. Let matchStr be ? ToString(? Get(match, "0")). <<*)
              let! matchStrop =<< get_head (ExecArrayExotic.array match_result) in
              let! matchStr =<< match matchStrop with | None => Error MatchError.AssertionFailed | Some s => Success s end in
              (*>> v. If matchStr is the empty String, then <<*)
              let! rx =<<
                   if (String.length matchStr) == 0 then
                     (*>> 1. Let thisIndex be ℝ(? ToLength(? Get(R, "lastIndex"))). <<*)
                     let thisIndex := RegExpInstance.lastIndex rx in
                     let! thisIndexnat =<< NonNegInt.from_int thisIndex in
                     (*>> 2. Let nextIndex be AdvanceStringIndex(S, thisIndex, fullUnicode). <<*)
                     let nextIndex := String.advanceStringIndex S thisIndexnat in
                     (*>> 3. Perform ? Set(R, "lastIndex", 𝔽(nextIndex), true). <<*)
                     Success (RegExpInstance.setLastIndex rx (BinInt.Z.of_nat nextIndex))
                   else Success rx in
              (*>> vi. Perform ? GeneratorYield(CreateIterResultObject(match, false)). <<*)
              Success (Some match_result, rx)
          end
      end in
    (*>> 2. Return CreateIteratorFromClosure(closure, "%RegExpStringIteratorPrototype%", %RegExpStringIteratorPrototype%). <<*)
    (* + NOTE: instead of mechanizing the whole iterator part of the spec, we just iterate it right away +*)
    let fix repeat_closure (previous_matches:list ExecArrayExotic) (R:RegExpInstance) (fuel:nat) : Result.Result (list ExecArrayExotic * RegExpInstance) MatchError :=
      match fuel with
      | O => out_of_fuel
      | S fuel' =>
          let! (it_match, it_R) =<< closure R in
          match it_match with
          | None => Success (previous_matches, it_R)
          | Some it_match => repeat_closure (List.app previous_matches (it_match::nil)) it_R fuel'
          end
      end in
    (* + each iteration of closure advances the index: we can use length S + 1 as fuel +*)
    repeat_closure nil R ((String.length S) +2).


  (** >>
      22.2.6.9 RegExp.prototype [ @@matchAll ] ( string )

      This method performs the following steps when called:
  <<*)
  Definition prototypeMatchAll (R :RegExpInstance) (S: String): Result.Result (list ExecArrayExotic * RegExpInstance) MatchError :=
    (*>> 5. Let flags be ? ToString(? Get(R, "flags")). <<*)
    let flags := RegExpInstance.originalFlags R in
    (*>> 9. If flags contains "g", let global be true. <<*)
    let global := RegExpFlags.g flags in
    (*>> 11. If flags contains "u", let fullUnicode be true. <<*)
    let fullUnicode := RegExpFlags.u flags in
    (*>> 13. Return CreateRegExpStringIterator(matcher, S, global, fullUnicode). <<*)
    createRegExpStringIterator R S global.

  (** >>
      22.1.3.13 String.prototype.matchAll ( regexp )

      This method performs a regular expression match of the String representing the this value against regexp and returns an iterator.
      Each iteration result's value is an Array containing the results of the match, or null if the String did not match.
  << *)
  Definition stringPrototypeMatchAll (R: RegExpInstance) (S: String): Result.Result (list ExecArrayExotic * RegExpInstance) MatchError :=
    (*>> b. iii. If ? ToString(flags) does not contain "g", throw a TypeError exception. <<*)
    match (RegExpFlags.g (RegExpInstance.originalFlags R)) with
    | false => Error MatchError.AssertionFailed
    | true =>
        (*>> 5. Return ? Invoke(rx, @@matchAll, « S »). <<*)
        prototypeMatchAll R S
    end.
End API.
