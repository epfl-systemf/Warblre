open Engines
open Printers

module Tester (P: EngineParameters) = struct
  open Engine(P)
  open Extracted.Notation
  open Printer(P)

  let list_to_string ls = P.Character.to_host (P.Character.list_to_string ls)
  let list_from_string str = P.Character.list_from_string (P.Character.from_host str)

  let pretty_print_result ls_input at (res: character coq_MatchResult) unicode =
    let input = list_to_string ls_input in
    match res with
    | Success (Some { MatchState.endIndex = i; MatchState.captures = captures; MatchState.input = _ }) -> 
      Printf.printf "%d characters ([%d-%d]) in '%s' (length=%d)\n" (i - at) at i input (List.length ls_input);
      let f id = 
        match List.nth captures (id - 1) with
        | None ->
            Printf.printf "Group %d: undefined\n" id
        | Some { CaptureRange.startIndex = s; CaptureRange.endIndex = e } ->
            Printf.printf "Group %d: '%s' ([%d-%d])\n" id (list_to_string (Utils.List.sublist ls_input s e)) s e
      in
      List.iter f (Extracted.List.Range.Nat.Length.range 1 (List.length captures))

    | Success None -> Printf.printf "nothing on '%s' \n" input

    | Failure OutOfFuel -> Printf.printf "Out of fuel on '%s' \n" input

    | Failure AssertionFailed -> Printf.printf "Assertion error during matching on '%s' \n" input

  let test_regex_using_record regex input at rer =
    match compilePattern regex rer with
    | Success matcher ->
      let ls_input = list_from_string input in
      Printf.printf "%s matched " (regex_to_string regex);
      pretty_print_result ls_input at (matcher ls_input at) true
      
    | Failure AssertionFailed -> Printf.printf "Assertion error during compilation \n"

  let test_regex regex input at ?(ignoreCase=false) ?(multiline=false) ?(dotAll=false) ?(unicode=false) () =
    let groups = (countGroups regex) in
    let rer = Extracted.({
      RegExpRecord.ignoreCase = ignoreCase;
      RegExpRecord.multiline = multiline;
      RegExpRecord.dotAll = dotAll;
      RegExpRecord.unicode = unicode;
      RegExpRecord.capturingGroupsCount = groups;
    }) in
    test_regex_using_record regex input at rer

  let test_exec_using_flags regex flags at input =
    match initialize regex flags with
    | Success r ->
      (match exec (setLastIndex r at) (Encoding.Utf16.list_from_string input) with
      | Success res -> Printf.printf "Matching %s on '%s':\n%s\n" (regex_to_string regex) input (exec_result_to_string res)
      | Failure AssertionFailed -> Printf.printf "Assertion failed during execution.\n"
      | Failure OutOfFuel -> Printf.printf "Out of fuel during execution.\n")
    | Failure _ -> Printf.printf "Assertion failed during initialization.\n"

  let test_exec ?(d=false) ?(g=false) ?(i=false) ?(m=false) ?(s=false) ?(y=false) regex ?(at=0) input =
    let flags = Extracted.({
      RegExpFlags.d = d;
      RegExpFlags.g = g;
      RegExpFlags.i = i;
      RegExpFlags.m = m;
      RegExpFlags.s = s;
      RegExpFlags.u = P.unicode;
      RegExpFlags.y = y;
    }) in
    test_exec_using_flags regex flags at input

  let compare_regexes_using_record regex1 regex2 input at rer: unit =
    match compilePattern regex1 rer, compilePattern regex2 rer with
    | Success m1, Success m2 ->
      let ls_input = list_from_string input in
      let res1 = (m1 ls_input at) in
      let res2 = (m2 ls_input at) in
      if res1 = res2 then
        (Printf.printf "The two regexes resulted in identical matches.\nMatched ";
        pretty_print_result ls_input at res1 true)
      else
        (Printf.printf "The two regexes resulted in different matches.\n";
        Printf.printf "%s matched " (regex_to_string regex1);
        pretty_print_result ls_input at res1 true;
        Printf.printf "%s matched " (regex_to_string regex2);
        pretty_print_result ls_input at res2 true)

    | Failure AssertionFailed, _ -> Printf.printf "Assertion error during compilation \n"
    | _, Failure AssertionFailed -> Printf.printf "Assertion error during compilation \n"

  let compare_regexes r1 r2 input at ?(ignoreCase=false) ?(multiline=false) ?(dotAll=false) ?(unicode=false) () =
    let groups = (countGroups r1) in
    let rer = Extracted.({
      RegExpRecord.ignoreCase = ignoreCase;
      RegExpRecord.multiline = multiline;
      RegExpRecord.dotAll = dotAll;
      RegExpRecord.unicode = unicode;
      RegExpRecord.capturingGroupsCount = groups;
    }) in
    compare_regexes_using_record r1 r2 input at rer
end

module Utf16Tester = Tester(Utf16Parameters)
module UnicodeTester = Tester(UnicodeParameters)