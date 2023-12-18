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
      }.

  Definition setlastindex (r:RegExpInstance) (index:integer) : RegExpInstance :=
    mkre (OriginalFlags r) (RegExpRecord r) (RegExpMatcher r) index.
                               
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
    mkre flags rer matcher integer_zero.


  Record ArrayExotic :=
    mkarray {
        index: nat;
        input: list Character;
        array: list (option (list Character));
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
  let indices: (list MatchRecord) := nil in
  (* 26. Let groupNames be a new empty List. *)
  let groupNames: (list (list Character)) := nil in
  (* 27. Append match to indices. *)
  let indices := match_rec :: indices in
  (* 28. Let matchedSubstr be GetMatchString(S, match). *)
  let! matchedSubstr =<< GetMatchString S match_rec in
  (* 29. Perform ! CreateDataPropertyOrThrow(A, "0", matchedSubstr). *)
  set A_array[0] := Some matchedSubstr in


    (* TODO: finish the rest when we have named groups *)
  
      Success (Exotic (mkarray A_index A_input A_array) (newInstance))
  end.
  
  
End Frontend.
Export Frontend.
