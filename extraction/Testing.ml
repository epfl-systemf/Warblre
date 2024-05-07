open Engines
open Printers

module Tester (P: EngineParameters) (S: Encoding.StringLike with type t := P.string) = struct
  module E = Engine(P)
  open E
  module Pr = Printer(P)(S)
  open Pr

  let string_to_engine_input str = P.String.list_from_string (S.of_string str)

  let test_regex_using_record regex input at rer =
    match compilePattern regex rer with
    | Success matcher ->
      let ls_input = string_to_engine_input input in
      Printf.printf "Regex %s on '%s' at %d:\n" (regex_to_string regex) input at;
      Printf.printf "%s\n" (match_result_to_string (matcher ls_input at))
    | Failure AssertionFailed -> Printf.printf "Assertion error during compilation \n"

  let test_regex regex input at ?(ignoreCase=false) ?(multiline=false) ?(dotAll=false) () =
    let groups = (countGroups regex) in
    let rer = Extracted.({
      RegExpRecord.ignoreCase = ignoreCase;
      RegExpRecord.multiline = multiline;
      RegExpRecord.dotAll = dotAll;
      RegExpRecord.unicode = ();
      RegExpRecord.capturingGroupsCount = groups;
    }) in
    test_regex_using_record regex input at rer

  let test_exec_using_flags regex flags at input =
    match initialize regex flags with
    | Success r ->
      (match exec (setLastIndex r at) (S.of_string input) with
      | Success res -> Printf.printf "Regex %s on '%s' at %d (using exec):\n%s\n" (regex_to_string regex) input at (exec_result_to_string res)
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
      RegExpFlags.u = ();
      RegExpFlags.y = y;
    }) in
    test_exec_using_flags regex flags at input

  let compare_regexes_using_record regex1 regex2 input at rer: unit =
    match compilePattern regex1 rer, compilePattern regex2 rer with
    | Success m1, Success m2 ->
      let ls_input = string_to_engine_input input in
      let res1 = (m1 ls_input at) in
      let res2 = (m2 ls_input at) in
      if res1 = res2 then
        (Printf.printf "The two regexes resulted in identical matches.\n";
        Printf.printf "%s\n" (match_result_to_string res1))
      else
        (Printf.printf "The two regexes resulted in different matches.\n";
        Printf.printf "Regex %s on '%s' at %d:\n" (regex_to_string regex1) input at;
        Printf.printf "%s\n" (match_result_to_string res1);
        Printf.printf "Regex %s on '%s' at %d:\n" (regex_to_string regex2) input at;
        Printf.printf "%s\n" (match_result_to_string res2))

    | Failure AssertionFailed, _ -> Printf.printf "Assertion error during compilation \n"
    | _, Failure AssertionFailed -> Printf.printf "Assertion error during compilation \n"

  let compare_regexes r1 r2 input at ?(ignoreCase=false) ?(multiline=false) ?(dotAll=false) () =
    let groups = (countGroups r1) in
    let rer = Extracted.({
      RegExpRecord.ignoreCase = ignoreCase;
      RegExpRecord.multiline = multiline;
      RegExpRecord.dotAll = dotAll;
      RegExpRecord.unicode = ();
      RegExpRecord.capturingGroupsCount = groups;
    }) in
    compare_regexes_using_record r1 r2 input at rer
end

