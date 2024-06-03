open Engines
open Printers

(*
  Some helper functions which combine multiple functions (e.g. compilation >> matching >> pretty_printing) into one, for more conveninent testing.
*)
module Tester (P: EngineParameters) (S: Encoding.StringLike with type t := P.string) = struct
  module E = Engine(P)
  open E
  module Pr = Printer(P)(S)
  open Pr

  let string_to_engine_input str = P.String.list_from_string (S.of_string str)

  let test_regex_using_record (regex: (P.character, _, _) Patterns.coq_Regex) input at rer =
    let matcher =  compilePattern regex rer in
    let ls_input = string_to_engine_input input in
    Printf.printf "Regex %s on '%s' at %d:\n" (regex_to_string regex) input at;
    Printf.printf "%s\n" (match_result_to_string (matcher ls_input (BigInt.of_int at)))

  (* Test the regex by using compilePattern (from the backend). *)
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
    let r = initialize regex flags in
    let res = exec (setLastIndex r (BigInt.of_int at)) (S.of_string input) in
    Printf.printf "Regex %s on '%s' at %d (using exec):\n%s\n" (regex_to_string regex) input at (exec_result_to_string res)

  (* Test the exec method (from the frontend). *)
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
    let m1 = compilePattern regex1 rer in
    let m2 = compilePattern regex2 rer in
    let ls_input = string_to_engine_input input in
    let res1 = (m1 ls_input (BigInt.of_int at)) in
    let res2 = (m2 ls_input (BigInt.of_int at)) in
    if res1 = res2 then (
      Printf.printf "The two regexes resulted in identical matches.\n";
      Printf.printf "%s\n" (match_result_to_string res1))
    else (
      Printf.printf "The two regexes resulted in different matches.\n";
      Printf.printf "Regex %s on '%s' at %d:\n" (regex_to_string regex1) input at;
      Printf.printf "%s\n" (match_result_to_string res1);
      Printf.printf "Regex %s on '%s' at %d:\n" (regex_to_string regex2) input at;
      Printf.printf "%s\n" (match_result_to_string res2))

  (* Compare the output of two regexes on the same input, to ensure they return the same result. *)
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

