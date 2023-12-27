From Coq Require Import List.
From Warblre Require Import Base Notation Patterns StaticSemantics Semantics Result List.

Import Result.Notations.
Local Open Scope result_flow.

Module Frontend.
  (* This module intentionally diverges from ECMAScript *)


  (* The phrase "the substring of S from inclusiveStart to exclusiveEnd" (where S is a String value or a sequence of code units and inclusiveStart and exclusiveEnd are integers) denotes the String value consisting of the consecutive code units of S beginning at index inclusiveStart and ending immediately before index exclusiveEnd (which is the empty String when inclusiveStart = exclusiveEnd). If the "to" suffix is omitted, the length of S is used as the value of exclusiveEnd. *)
  Fixpoint prefix {A:Type} (l:list A) (len:nat) : list A :=
    match len with
    | 0 => nil
    | S len' =>
        match l with
        | nil => nil
        | e::l' => e :: (prefix l' len')
        end
    end.

  Fixpoint substring {A:Type} (l:list A) (mstart:nat) (mend:nat): list A :=
    match mstart with
    | 0 => prefix l mend
    | S mstart' =>
        match l with
        | nil => nil
        | e::l' => substring l' (mstart') (mend-1)
        end
    end.

  (* checks that a pattern contains a group name somewhere *)
  Fixpoint containsgroupname (r:Patterns.Regex) : bool :=
    match r with
    | Empty => false
    | Char _ => false
    | Disjunction r1 r2 => orb (containsgroupname r1) (containsgroupname r2)
    | Quantified r1 _ => containsgroupname r1
    | Seq r1 r2 => orb (containsgroupname r1) (containsgroupname r2)
    | Group nameop r1 =>
        match nameop with
        | Some _ => true
        | None => containsgroupname r1
        end
    | Lookahead r1 => containsgroupname r1
    | NegativeLookahead r1 => containsgroupname r1
    | Lookbehind r1 => containsgroupname r1
    | NegativeLookbehind r1 => containsgroupname r1
    | BackReference _ => false
    end.
             
  
  Definition integer_zero : integer := BinNums.Z0.

  Definition to_non_neg (i:integer) : Result non_neg_integer MatchError :=
    assert! (BinInt.Z.geb i integer_zero);
  Success (BinInt.Z.to_nat i).
  
  Record RegExpFlags :=
    mkflags {
        d: bool;
        g: bool;
        i: bool;
        m: bool;
        s: bool;
        u: bool;
        v: bool;
        y: bool;
        }.
  (* TODO: add a function that generates the RegExp record from flags when this record is complete (it should hold some of the RegExpFlags) *)
  
  Record RegExpInstance :=
    mkre {
        OriginalFlags: RegExpFlags;
        RegExpRecord: RegExp;
        RegExpMatcher: list Character -> non_neg_integer -> MatchResult;
        lastIndex: integer;
        pattern: Patterns.Regex;
      }.

  Definition setlastindex (r:RegExpInstance) (index:integer) : RegExpInstance :=
    mkre (OriginalFlags r) (RegExpRecord r) (RegExpMatcher r) index (pattern r).
                               
  (* 22.2.7.5 Match Records
A Match Record is a Record value used to encapsulate the start and end indices of a regular expression match or capture. *)
  Record MatchRecord :=
    mkrec {
        StartIndex: nat;
        EndIndex: nat;
      }.
  (* here we are missing the invariant that endIndex is bigger than start index *)
  (* So let's define a constructor that checks this invariant *)
  Definition MakeMatchRecord (mstart:nat) (mend:integer) : Result.Result MatchRecord MatchError :=
    let! enat =<< to_non_neg mend in
    assert! (enat >? mstart);
  Success (mkrec mstart enat).

  (* 22.2.7.6 GetMatchString ( S, match ) *)
  (* The abstract operation GetMatchString takes arguments S (a String) and match (a Match Record) and returns a String. It performs the following steps when called: *)
  Definition GetMatchString (S:list Character) (match_rec:MatchRecord) : Result.Result (list Character) MatchError :=
    (* 1. Assert: match.[[StartIndex]] ≤ match.[[EndIndex]] ≤ the length of S. *)
    assert! ((StartIndex match_rec) <=? (EndIndex match_rec));
  assert! ((EndIndex match_rec) <=? List.length S);
  (* 2. Return the substring of S from match.[[StartIndex]] to match.[[EndIndex]]. *)
  Success (substring S (StartIndex match_rec) (EndIndex match_rec)).
    
  
  (* 22.2.3.3 RegExpInitialize ( obj, pattern, flags ) *)
  Definition RegExpInitialize (pattern:Regex) (flags:RegExpFlags) : RegExpInstance :=
    (* Let capturingGroupsCount be CountLeftCapturingParensWithin(parseResult). *)
    let capturingGroupsCount := countLeftCapturingParensWithin pattern nil in
    (* Let rer be the RegExp Record { [[IgnoreCase]]: i, [[Multiline]]: m, [[DotAll]]: s, [[Unicode]]: u, [[UnicodeSets]]: v, [[CapturingGroupsCount]]: capturingGroupsCount }. *)
    let rer := RegExp.make capturingGroupsCount in
    (* Set obj.[[RegExpMatcher]] to CompilePattern of parseResult with argument rer. *)
    let matcher := Semantics.compilePattern pattern rer in
    (* Perform ? Set(obj, "lastIndex", +0𝔽, true) *)
    mkre flags rer matcher integer_zero pattern.


  (** * Defining Some Types *)

  (* the groups that are returned inside the obejct returned by RegExpBuiltinExec *)
  Definition groups_map : Type := list (GroupName * option (list Character)).
  
  (* the return result of RegExpBuiltinExec *)
  Record ArrayExotic :=
    mkarray {
        index: nat;
        input: list Character;
        array: list (option (list Character)); 
        groups: option groups_map;
        indices_array: option (list (option (nat*nat)));
        indices_groups: option (list (GroupName * option (nat*nat)));
      }.

  (* 22.2.7.3 AdvanceStringIndex ( S, index, unicode ) *)
  (* The abstract operation AdvanceStringIndex takes arguments S (a String), index (a non-negative integer), and unicode (a Boolean) and returns an integer. It performs the following steps when called: *)

  Definition AdvanceStringIndex (S:list Character) (index:nat) (unicode:bool) : Result.Result nat MatchError :=
    (* 1. Assert: index ≤ 2^53 - 1. *)
    assert! (index <? 9007199254740991)%nat;
  Success (Nat.add index 1)%nat.
  (* TODO: this is incomplete, change it when you have unicode *)

  (* 22.2.7.4 GetStringIndex ( S, codePointIndex ) *)
  Definition GetStringIndex (S:list Character) (codePointIndex:integer) : integer := codePointIndex.
  (* TODO: this is incomplete, change it when you have unicode *)

  Inductive ExecResult :=
  | Null: RegExpInstance -> ExecResult (* also returns modifications to the RegExpInstance Object *)
  | Exotic: ArrayExotic -> RegExpInstance -> ExecResult.
  (* todo: array exotic *)

  (* The inner repeat loop can either make the whole function terminate *)
  (* Or it lets the whole function go on, but defines (r:MatchState) and (lastIndex:nat) *)
  Inductive LoopResult :=
  | Terminates: ExecResult -> LoopResult
  | Continues: MatchState -> nat -> LoopResult.


  (** * Modified RegExpBuiltinExec  *)

  Inductive SearchGroup :=
  | SearchFrom: nat -> SearchGroup
  | Found: option GroupName -> SearchGroup.

  (* Finds the ith group name, where i=0 designates the first group inside the pattern *)
  Fixpoint find_group_name (r:Regex) (i:nat) : SearchGroup :=
    match r with
    | Empty => SearchFrom i
    | Char _ => SearchFrom i
    | Disjunction r1 r2 =>
        match (find_group_name r1 i) with
        | Found o => Found o
        | SearchFrom i' => find_group_name r2 i'
        end
    | Quantified r1 q => find_group_name r1 i
    | Seq r1 r2 =>
        match (find_group_name r1 i) with
        | Found o => Found o
        | SearchFrom i' => find_group_name r2 i'
        end
    | Group name r1 =>
        match i with
        | O => Found name
        | S i' => find_group_name r1 i'
        end
    | Lookahead r1 => find_group_name r1 i
    | NegativeLookahead r1 => find_group_name r1 i
    | Lookbehind r1 => find_group_name r1 i
    | NegativeLookbehind r1 => find_group_name r1 i
    | BackReference _ => SearchFrom i
    end.

  Definition find_nth_group_name (r:Regex) (n:nat) : Result.Result (option GroupName) MatchError :=
    match n with
    | O => Success None         (* group 0 is never named *)
    | S i =>
        match (find_group_name r i) with
        | Found go => Success go
        | SearchFrom _ => assertion_failed (* the n-th group was not defined in r *)
        end
    end.
        

  (* transforms a capture into a capturedValue, a substring of the original string *)
  Definition capture_to_value (S:list Character) (cI:option CaptureRange) : Result.Result (option (list Character)) MatchError :=
    match cI with
    (* b. If captureI is undefined, then
    i. Let capturedValue be undefined. *)
    | None => Success None
    (* c. Else, *)
    | Some captureI =>
        (* i. Let captureStart be captureI.[[StartIndex]]. *)
        let captureStart := CaptureRange.startIndex captureI in
        let! captureStart_non_neg =<< to_non_neg captureStart in
        (* ii. Let captureEnd be captureI.[[EndIndex]]. *)
        let captureEnd := CaptureRange.endIndex captureI in
        (* iii. If fullUnicode is true, then
           1. Set captureStart to GetStringIndex(S, captureStart).
           2. Set captureEnd to GetStringIndex(S, captureEnd). *)
        (* TODO *)
        (* iv. Let capture be the Match Record { [[StartIndex]]: captureStart, [[EndIndex]]: captureEnd }. *)
        let! capture =<< MakeMatchRecord captureStart_non_neg captureEnd in
        (* v. Let capturedValue be GetMatchString(S, capture). *)
        let! capturedValue =<< GetMatchString S capture in
        Success (Some capturedValue)
    end.

  (* computes the array part of the Exotic Array, but only for captures with an index >= 1 *)
  Fixpoint captures_to_array (S:list Character) (captures:list (option CaptureRange)) : Result.Result (list (option (list Character))) MatchError :=
    (* 33. For each integer i such that 1 ≤ i ≤ n, in ascending order, do *)
    match captures with
    | nil => Success nil
    (* a. Let captureI be ith element of r's captures List. *)
    | captureI::captures' =>
        let! capturedValue =<< capture_to_value S captureI in
        let! next =<< captures_to_array S captures' in
        (* d. Perform ! CreateDataPropertyOrThrow(A, ! ToString(𝔽(i)), capturedValue). *)
        Success (capturedValue::next)
    end.

  (* i is the index of the first group in the captures list (initially, 1) *)
  Fixpoint captures_to_groupsmap (R:Regex) (S:list Character) (captures:list (option CaptureRange)) (i:nat): Result.Result groups_map MatchError :=
    match captures with
    | nil => Success nil
    | captureI::captures' =>
        let! capturedValue =<< capture_to_value S captureI in
        let! groupname =<< find_nth_group_name R i in
        let! next =<< captures_to_groupsmap R S captures' (i+1) in
        (* e. If the ith capture of R was defined with a GroupName, then *)
        match groupname with
        | None => Success next
        (* i. Let s be the CapturingGroupName of that GroupName. *)
        (* ii. Perform ! CreateDataPropertyOrThrow(groups, s, capturedValue). *)
        | Some s => Success ((s,capturedValue)::next)
        end
    end.

  (* computes the groups map, associating each group name to its captured value *)
  Definition captures_to_groups_map (R:Regex) (S:list Character) (captures: list (option CaptureRange)) : Result.Result groups_map MatchError :=
    captures_to_groupsmap R S captures 1%nat.


  Fixpoint captures_to_groupnames (R:Regex) (captures:list (option CaptureRange)) (i:nat): Result.Result (list (option GroupName)) MatchError :=
    match captures with
    | nil => Success nil
    | captureI::captures' =>
        let! groupname =<< find_nth_group_name R i in
        let! next =<< captures_to_groupnames R captures' (i+1) in
        match groupname with
        (* iii. Append s to groupNames. *)
        | Some s => Success ((Some s)::next)
        (* f. Else, *)
        (*i. Append undefined to groupNames. *)
        | None => Success (None::next)
        end
    end.

  Definition captures_to_group_names (R:Regex)  (captures:list (option CaptureRange)): Result.Result (list (option GroupName)) MatchError :=
    captures_to_groupnames R captures 1%nat.

  (* transforms a capture into a matchRecord *)
  Definition capture_to_record (cI:option CaptureRange) : Result.Result (option MatchRecord) MatchError :=
    match cI with
    (* b. If captureI is undefined, then
    i. Let capturedValue be undefined. *)
    | None => Success None
    (* c. Else, *)
    | Some captureI =>
        (* i. Let captureStart be captureI.[[StartIndex]]. *)
        let captureStart := CaptureRange.startIndex captureI in
        let! captureStart_non_neg =<< to_non_neg captureStart in
        (* ii. Let captureEnd be captureI.[[EndIndex]]. *)
        let captureEnd := CaptureRange.endIndex captureI in
        (* iii. If fullUnicode is true, then
           1. Set captureStart to GetStringIndex(S, captureStart).
           2. Set captureEnd to GetStringIndex(S, captureEnd). *)
        (* TODO *)
        (* iv. Let capture be the Match Record { [[StartIndex]]: captureStart, [[EndIndex]]: captureEnd }. *)
        let! capture =<< MakeMatchRecord captureStart_non_neg captureEnd in
        (* vi. Append capture to indices. *)
        Success (Some capture)
    end.

  (* computes the indices list *)
  Fixpoint captures_to_indices (captures:list (option CaptureRange)) : Result.Result (list (option MatchRecord)) MatchError :=
    (* 33. For each integer i such that 1 ≤ i ≤ n, in ascending order, do *)
    match captures with
    | nil => Success nil
    (* a. Let captureI be ith element of r's captures List. *)
    | captureI::captures' =>
        let! record =<< capture_to_record captureI in
        let! next =<< captures_to_indices captures' in
        Success (record::next)
    end.


  (*  22.2.7.7 GetMatchIndexPair ( S, match )

The abstract operation GetMatchIndexPair takes arguments S (a String) and match (a Match Record) and returns an Array. It performs the following steps when called:
   *)

  Definition GetMatchIndexPair (S:list Character) (match_rec:MatchRecord) : Result.Result (nat * nat) MatchError :=
    (* 1. Assert: match.[[StartIndex]] ≤ match.[[EndIndex]] ≤ the length of S. *)
    assert! ((StartIndex match_rec) <=? (EndIndex match_rec));
  assert! ((EndIndex match_rec) <=? List.length S);
  (* 2. Return CreateArrayFromList(« 𝔽(match.[[StartIndex]]), 𝔽(match.[[EndIndex]]) »). *)
  Success (StartIndex match_rec, EndIndex match_rec).
    
  
  (* 22.2.7.8 MakeMatchIndicesIndexPairArray ( S, indices, groupNames, hasGroups )

The abstract operation MakeMatchIndicesIndexPairArray takes arguments S (a String), indices (a List of either Match Records or undefined), groupNames (a List of either Strings or undefined), and hasGroups (a Boolean) and returns an Array. It performs the following steps when called: *)
  (* NOTE: we separate this in two functions: one computing the indices array, the other one computing the groups *)
  (* NOTE: here [hasGroup] means "has names groups" *)

  Fixpoint MakeMatchIndicesArray (S:list Character) (indices:list (option MatchRecord)): Result.Result (list (option (nat*nat))) MatchError :=
    match indices with
    | nil => Success nil
    (* a. Let matchIndices be indices[i]. *)
    | matchIndices::indices' =>
        let! matchIndexPair =<<
             match matchIndices with
             (* b. If matchIndices is not undefined, then *)
             | Some match_rec =>
                 (* i. Let matchIndexPair be GetMatchIndexPair(S, matchIndices). *)
                 let! mpair =<< GetMatchIndexPair S match_rec in
                 Success (Some mpair)
             (* c. Else, *)
             (* i. Let matchIndexPair be undefined *)
             | None => Success None
                               
             end in
        let! next =<< MakeMatchIndicesArray S indices' in
        (* d. Perform ! CreateDataPropertyOrThrow(A, ! ToString(𝔽(i)), matchIndexPair). *)
        Success (matchIndexPair::next)
    end.

  (* assuming that indices does not contain the first element *)
  Fixpoint MakeMatchIndicesGroupList (S:list Character) (indices:list (option MatchRecord)) (groupNames:list (option GroupName)): Result.Result (list (GroupName * option (nat*nat))) MatchError :=
     match indices with
    | nil => Success nil
    (* a. Let matchIndices be indices[i]. *)
    | matchIndices::indices' =>
        let! matchIndexPair =<<
             match matchIndices with
             (* b. If matchIndices is not undefined, then *)
             | Some match_rec =>
                 (* i. Let matchIndexPair be GetMatchIndexPair(S, matchIndices). *)
                 let! mpair =<< GetMatchIndexPair S match_rec in
                 Success (Some mpair)
             (* c. Else, *)
             (* i. Let matchIndexPair be undefined *)
             | None => Success None                       
             end in
        match groupNames with
        | nil => assertion_failed
        | gn::groupNames' =>
            let! next =<< MakeMatchIndicesGroupList S indices' groupNames' in
            match gn with
            | None => Success next
            (* e. If i > 0 and groupNames[i - 1] is not undefined, then *)
            (* ii. Perform ! CreateDataPropertyOrThrow(groups, groupNames[i - 1], matchIndexPair). *)
            | Some name => Success ((name,matchIndexPair)::next)
            end
        end
     end.

  Definition MakeMatchIndicesGroups (S:list Character) (indices:list (option MatchRecord)) (groupNames:list (option GroupName)) (hasGroups:bool): Result.Result (option (list (GroupName * option (nat*nat)))) MatchError :=
    (* 1. Let n be the number of elements in indices. *)
    let n := List.length indices in
    (* 2. Assert: n < 232 - 1. *)
    assert! (n <? 4294967295)%nat;
  (* 3. Assert: groupNames has n - 1 elements. *)
  assert! (List.length groupNames =? n-1)%nat;
    match hasGroups with
    | false => Success None
    | true => 
        match indices with
        | indices_zero::indices' =>
            let! groups =<< MakeMatchIndicesGroupList S indices' groupNames in
            Success (Some groups)
        | nil => assertion_failed
        end
    end.
    
    
  
  
  (* 22.2.7.2 RegExpBuiltinExec ( R, S ) *)
  (* TODO: here S does not describe the input in its string form, but already as a list of characters *)
  (* this will need to changr as we implement unicode and the two ways to go from a string to a list of characters *)
  (* The abstract operation RegExpBuiltinExec takes arguments R (an initialized RegExp instance) and S (a String) and returns either a normal completion containing either an Array exotic object or null, or a throw completion. It performs the following steps when called: *)

  Definition RegExpBuiltinExec (R:RegExpInstance) (S:list Character) (fuel:nat): Result.Result ExecResult MatchError :=
    (* 1. Let length be the length of S. *)
    let length := List.length S in
    (* 2. Let lastIndex be ℝ(? ToLength(? Get(R, "lastIndex"))). *)
    let lastIndex := lastIndex R in
    (* 3. Let flags be R.[[OriginalFlags]]. *)
    let flags := OriginalFlags R in
    (* 4. If flags contains "g", let global be true; else let global be false. *)
    let global := g flags in
    (* 5. If flags contains "y", let sticky be true; else let sticky be false. *)
    let sticky := y flags in
    (* 6. If flags contains "d", let hasIndices be true; else let hasIndices be false. *)
    let hasIndices := d flags in
    (* 7. If global is false and sticky is false, set lastIndex to 0. *)
    let lIndex:integer := if (andb (negb global) (negb sticky)) then integer_zero else lastIndex in
    let! lastIndex: nat =<< to_non_neg lIndex in
    (* 8. Let matcher be R.[[RegExpMatcher]]. *)
    let matcher := RegExpMatcher R in
    (* 9. If flags contains "u" or flags contains "v", let fullUnicode be true; else let fullUnicode be false. *)
    let fullUnicode := if (orb (u flags) (v flags)) then true else false in
    (* 10. Let matchSucceeded be false. *)
    let matchSucceeded := false in
    (* 11. If fullUnicode is true, let input be StringToCodePoints(S). Otherwise, let input be a List whose elements are the code units that are the elements of S. *)
    (* TODO: go from string to list at this point *)
    let input := S in
    (* 12. NOTE: Each element of input is considered to be a character. *)
    (* We change the repeat loop to a recursive function with fuel *)
    let fix repeatloop (lastIndex:nat) (fuel:nat): Result LoopResult MatchError :=
      match fuel with
      | 0 => out_of_fuel
      | S fuel' =>
          (* a. If lastIndex > length, then *)
          if (lastIndex >? length)%nat then
            (* i. If global is true or sticky is true, then *)
            let nextInstance := if (orb global sticky) then
                                  (* 1. Perform ? Set(R, "lastIndex", +0𝔽, true). *)
                                  setlastindex R integer_zero
                                else R in
            (* ii. Return null. *)
            Success (Terminates (Null nextInstance))
          else
            (* b. Let inputIndex be the index into input of the character that was obtained from element lastIndex of S. *)
            let inputIndex := lastIndex in
            (* c. Let r be matcher(input, inputIndex). *)
            let! r:(option MatchState) =<< matcher input inputIndex in
            (* d. If r is failure, then *)
            if r is (failure) then
              (* i. If sticky is true, then *)
              if sticky then
                (* 1. Perform ? Set(R, "lastIndex", +0𝔽, true). *)
                let nextInstance := setlastindex R integer_zero in
                (* 2. Return null. *)
                Success (Terminates (Null nextInstance))
              else
                (* ii. Set lastIndex to AdvanceStringIndex(S, lastIndex, fullUnicode). *)
                let! lastIndex =<< AdvanceStringIndex S lastIndex fullUnicode in
                repeatloop lastIndex fuel' 
                           (* e. Else *)
            else
              (* i. Assert: r is a MatchState. *)
              assert! (r is (Some _));
              destruct! Some r <- (r:option MatchState) in
              (*   ii. Set matchSucceeded to true. *)
              Success (Continues r lastIndex)
  end in
  let! repeatresult =<< repeatloop lastIndex fuel in
  match repeatresult with
  | Terminates execresult => Success (execresult)
  | Continues r lastIndex =>
      (* 14. Let e be r.[[EndIndex]]. *)
      let e := MatchState.endIndex r in
      (* 15. If fullUnicode is true, set e to GetStringIndex(S, e). *)
      let e := if fullUnicode then GetStringIndex S e else e in
      (* 16. If global is true or sticky is true, then *)
      let newInstance := if (orb global sticky) then
                           (* a. Perform ? Set(R, "lastIndex", 𝔽(e), true). *)
                           setlastindex R e
                         else R in
      (* 17. Let n be the number of elements in r.[[Captures]]. *)
      let n := List.length (MatchState.captures r) in
      (* 18. Assert: n = R.[[RegExpRecord]].[[CapturingGroupsCount]]. *)
      assert! (n =? RegExp.capturingGroupsCount (RegExpRecord newInstance))%nat;
  (* 19. Assert: n < 2^32 - 1. *)
  assert! (n <? 4294967295)%nat;
  (* 22. Perform ! CreateDataPropertyOrThrow(A, "index", 𝔽(lastIndex)). *)
  let A_index := lastIndex in
  (* 23. Perform ! CreateDataPropertyOrThrow(A, "input", S). *)
  let A_input := S in
  (* 24. Let match be the Match Record { [[StartIndex]]: lastIndex, [[EndIndex]]: e }. *)
  let! match_rec =<< MakeMatchRecord lastIndex e in
  (* 28. Let matchedSubstr be GetMatchString(S, match). *)
  let! matchedSubstr =<< GetMatchString S match_rec in
  (* 29. Perform ! CreateDataPropertyOrThrow(A, "0", matchedSubstr). *)
  let A_array_zero := Some matchedSubstr in
  let! A_array_next =<< captures_to_array S (MatchState.captures r) in
  let A_array := A_array_zero::A_array_next in
  (* 21. Assert: The mathematical value of A's "length" property is n + 1. *)
  assert! (List.length A_array =? n+1);
  let! groupsmap =<< captures_to_groups_map (pattern R) S (MatchState.captures r) in
  (* 30. If R contains any GroupName, then *)
  let hasGroups := containsgroupname (pattern R) in  
  let A_groups := if hasGroups then Some groupsmap
                  (* 31. Else, *)
                  (* a. Let groups be undefined. *)
                  else None
  in
  (* 27. Append match to indices. *)
  let! indices_next =<< captures_to_indices (MatchState.captures r) in
  let indices := (Some match_rec) :: indices_next in
  let! groupNames =<< captures_to_group_names (pattern R) (MatchState.captures r) in
  (* 34. a. Let indicesArray be MakeMatchIndicesIndexPairArray(S, indices, groupNames, hasGroups). *)
  let! A_indices_array =<<
       if hasIndices then
         let! array =<< MakeMatchIndicesArray S indices in
         Success (Some array)
       else Success None in
  let! A_indices_groups =<<
       if hasIndices then MakeMatchIndicesGroups S indices groupNames hasGroups
       else Success None in
  Success (Exotic (mkarray A_index A_input A_array A_groups A_indices_array A_indices_groups) (newInstance))
  end.





  (* Deprecated Version *)
  (*  Definition RegExpBuiltinExec (R:RegExpInstance) (S:list Character) (fuel:nat): Result.Result ExecResult MatchError :=
    (* 1. Let length be the length of S. *)
    let length := List.length S in
    (* 2. Let lastIndex be ℝ(? ToLength(? Get(R, "lastIndex"))). *)
    let lastIndex := lastIndex R in
    (* 3. Let flags be R.[[OriginalFlags]]. *)
    let flags := OriginalFlags R in
    (* 4. If flags contains "g", let global be true; else let global be false. *)
    let global := g flags in
    (* 5. If flags contains "y", let sticky be true; else let sticky be false. *)
    let sticky := y flags in
    (* 6. If flags contains "d", let hasIndices be true; else let hasIndices be false. *)
    let hasIndices := d flags in
    (* 7. If global is false and sticky is false, set lastIndex to 0. *)
    let lIndex:integer := if (andb (negb global) (negb sticky)) then integer_zero else lastIndex in
    let! lastIndex: nat =<< to_non_neg lIndex in
    (* 8. Let matcher be R.[[RegExpMatcher]]. *)
    let matcher := RegExpMatcher R in
    (* 9. If flags contains "u" or flags contains "v", let fullUnicode be true; else let fullUnicode be false. *)
    let fullUnicode := if (orb (u flags) (v flags)) then true else false in
    (* 10. Let matchSucceeded be false. *)
    let matchSucceeded := false in
    (* 11. If fullUnicode is true, let input be StringToCodePoints(S). Otherwise, let input be a List whose elements are the code units that are the elements of S. *)
    (* TODO: go from string to list at this point *)
    let input := S in
    (* 12. NOTE: Each element of input is considered to be a character. *)
    (* We change the repeat loop to a recursive function with fuel *)
    let fix repeatloop (lastIndex:nat) (fuel:nat): Result LoopResult MatchError :=
      match fuel with
      | 0 => out_of_fuel
      | S fuel' =>
          (* a. If lastIndex > length, then *)
          if (lastIndex >? length)%nat then
            (* i. If global is true or sticky is true, then *)
            let nextInstance := if (orb global sticky) then
                                  (* 1. Perform ? Set(R, "lastIndex", +0𝔽, true). *)
                                  setlastindex R integer_zero
                                else R in
            (* ii. Return null. *)
            Success (Terminates (Null nextInstance))
          else
            (* b. Let inputIndex be the index into input of the character that was obtained from element lastIndex of S. *)
            let inputIndex := lastIndex in
            (* c. Let r be matcher(input, inputIndex). *)
            let! r:(option MatchState) =<< matcher input inputIndex in
            (* d. If r is failure, then *)
            if r is (failure) then
              (* i. If sticky is true, then *)
              if sticky then
                (* 1. Perform ? Set(R, "lastIndex", +0𝔽, true). *)
                let nextInstance := setlastindex R integer_zero in
                (* 2. Return null. *)
                Success (Terminates (Null nextInstance))
              else
                (* ii. Set lastIndex to AdvanceStringIndex(S, lastIndex, fullUnicode). *)
                let! lastIndex =<< AdvanceStringIndex S lastIndex fullUnicode in
                repeatloop lastIndex fuel' 
                           (* e. Else *)
            else
              (* i. Assert: r is a MatchState. *)
              assert! (r is (Some _));
              destruct! Some r <- (r:option MatchState) in
              (*   ii. Set matchSucceeded to true. *)
              Success (Continues r lastIndex)
  end in
  let! repeatresult =<< repeatloop lastIndex fuel in
  match repeatresult with
  | Terminates execresult => Success (execresult)
  | Continues r lastIndex =>
      (* 14. Let e be r.[[EndIndex]]. *)
      let e := MatchState.endIndex r in
      (* 15. If fullUnicode is true, set e to GetStringIndex(S, e). *)
      let e := if fullUnicode then GetStringIndex S e else e in
      (* 16. If global is true or sticky is true, then *)
      let newInstance := if (orb global sticky) then
                           (* a. Perform ? Set(R, "lastIndex", 𝔽(e), true). *)
                           setlastindex R e
                         else R in
      (* 17. Let n be the number of elements in r.[[Captures]]. *)
      let n := List.length (MatchState.captures r) in
      (* 18. Assert: n = R.[[RegExpRecord]].[[CapturingGroupsCount]]. *)
      assert! (n =? RegExp.capturingGroupsCount (RegExpRecord newInstance))%nat;
  (* 19. Assert: n < 2^32 - 1. *)
  assert! (n <? 4294967295)%nat;
  (* 20. Let A be ! ArrayCreate(n + 1). *)
  let A_array:(list (option (list Character))) := List.repeat None (n+1) in
  (* 21. Assert: The mathematical value of A's "length" property is n + 1. *)
  assert! (List.length A_array =? n+1);
  (* 22. Perform ! CreateDataPropertyOrThrow(A, "index", 𝔽(lastIndex)). *)
  let A_index := lastIndex in
  (* 23. Perform ! CreateDataPropertyOrThrow(A, "input", S). *)
  let A_input := S in
  (* 24. Let match be the Match Record { [[StartIndex]]: lastIndex, [[EndIndex]]: e }. *)
  let! match_rec =<< MakeMatchRecord lastIndex e in
  (* 25. Let indices be a new empty List. *)
  let indices: (list (option MatchRecord)) := nil in
  (* 26. Let groupNames be a new empty List. *)
  let groupNames: (list GroupName) := nil in
  (* 27. Append match to indices. *)
  let indices := (Some match_rec) :: indices in
  (* 28. Let matchedSubstr be GetMatchString(S, match). *)
  let! matchedSubstr =<< GetMatchString S match_rec in
  (* 29. Perform ! CreateDataPropertyOrThrow(A, "0", matchedSubstr). *)
  set A_array[0] := Some matchedSubstr in
  (* 30. If R contains any GroupName, then *)
  let hasGroups := containsgroupname (pattern R) in  
  let groups := if hasGroups then
                  (* a. Let groups be OrdinaryObjectCreate(null). *)
                  Some nil
                    (* b. Let hasGroups be true. *)
                else
                  (* 31. Else, *)
                  (* a. Let groups be undefined. *)
                  None
                    (* b. Let hasGroups be false. *)
  in
  (* 32. Perform ! CreateDataPropertyOrThrow(A, "groups", groups). *)
  (* 33. For each integer i such that 1 ≤ i ≤ n, in ascending order, do *)
  let fix forloop (i:nat) (indices:list (option MatchRecord)) (groupNames:list GroupName) (fuel:nat): Result.Result (list (option MatchRecord) * list GroupName) MatchError:=
    match fuel with
    | O => out_of_fuel
    | S fuel' => 
        (* a. Let captureI be ith element of r.[[Captures]]. *)
        let! captureI =<< (MatchState.captures r)[i] in
        let! (capturedValue, indices) : (option (list Character) * list (option MatchRecord)) =<<
          match captureI with
          (* b. If captureI is undefined, then *)
          | None =>
              (* i. Let capturedValue be undefined. *)
              let capturedValue := None in
              (* ii. Append undefined to indices. *)
              Success (capturedValue, None::indices)
          (* c. Else, *)
          | Some captureI =>
              (* i. Let captureStart be captureI.[[StartIndex]]. *)
              let captureStart := CaptureRange.startIndex captureI in
              let! captureStart_non_neg =<< to_non_neg captureStart in
              (* ii. Let captureEnd be captureI.[[EndIndex]]. *)
              let captureEnd := CaptureRange.endIndex captureI in
              (* iii. If fullUnicode is true, then
    1. Set captureStart to GetStringIndex(S, captureStart).
    2. Set captureEnd to GetStringIndex(S, captureEnd). *)
              (* TODO *)
              (* iv. Let capture be the Match Record { [[StartIndex]]: captureStart, [[EndIndex]]: captureEnd }. *)
              let! capture =<< MakeMatchRecord captureStart_non_neg captureEnd in
              (* v. Let capturedValue be GetMatchString(S, capture). *)
              let! capturedValue =<< GetMatchString S capture in
              (* vi. Append capture to indices. *)
              Success (Some capturedValue, (Some capture)::indices)
          end in
        (* d. Perform ! CreateDataPropertyOrThrow(A, ! ToString(𝔽(i)), capturedValue). *)
        set A_array[i] := Some capturedValue in

  (* e. f. TODO *)
  if (i >=? n)%nat then Success (indices, groupNames)
  else forloop (i+1) indices groupNames fuel'
    end in
  let! (indices, groupNames) =<< forloop 1%nat indices groupNames fuel in
  
      Success (Exotic (mkarray A_index A_input A_array groups) (newInstance))
  end. *)
  
End Frontend.
Export Frontend.
