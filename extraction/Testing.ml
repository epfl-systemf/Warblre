open Engines

module Tester (E: Engine) = struct
  include E
  open Extracted.Notation

  let pretty_print_result ls_input at (res: character coq_MatchResult) unicode =
    let input = list_to_string ls_input in
    match res with
    | Success (Some { MatchState.endIndex = i; MatchState.captures = captures; MatchState.input = _ }) -> 
      Printf.printf "Matched %d characters ([%d-%d]) in '%s' (length=%d)\n" (i - at) at i input (List.length ls_input);
      let f id = 
        match List.nth captures (id - 1) with
        | None ->
            Printf.printf "Group %d: undefined\n" id
        | Some { CaptureRange.startIndex = s; CaptureRange.endIndex = e } ->
            Printf.printf "Group %d: '%s' ([%d-%d])\n" id (list_to_string (Utils.List.sublist ls_input s e)) s e
      in
      List.iter f (Extracted.List.Range.Nat.Length.range 1 (List.length captures))

    | Success None -> Printf.printf "No match on '%s' \n" input

    | Failure OutOfFuel -> Printf.printf "Out of fuel on '%s' \n" input

    | Failure AssertionFailed -> Printf.printf "Assertion error during matching on '%s' \n" input

  let test_regex_using_record regex input at rer =
    match compilePattern regex rer with
    | Success matcher ->
      let ls_input = list_from_string input in
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

  let compare_regexes_using_record regex1 regex2 input at rer: unit =
    match compilePattern regex1 rer, compilePattern regex2 rer with
    | Success m1, Success m2 ->
      let ls_input = list_from_string input in
      let res1 = (m1 ls_input at) in
      let res2 = (m2 ls_input at) in
      if res1 = res2 then
        (Printf.printf "The two regexes resulted in identical matches.\n";
        pretty_print_result ls_input at res1 true)
      else
        (Printf.printf "The two regexes resulted in different matches.\n";
        pretty_print_result ls_input at res1 true;
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

module Utf16Tester = Tester(Engines.Utf16Engine)
module UnicodeTester = Tester(Engines.UnicodeEngine)