open Extracted.Notation

let rec drop n ls = 
  if n <= 0 then
    ls
  else
    match ls with
    | _ :: ls' -> drop (n-1) ls'
    | [] -> []

let rec take n ls = 
  if n <= 0 then
    []
  else
    match ls with
    | h :: ls' -> h :: (take (n-1) ls')
    | [] -> []

let to_list s = List.init (String.length s) (String.get s)
let from_list ls = String.init (List.length ls) (List.nth ls)

let pretty_print_result sinput at (res: Extracted.Notation.coq_MatchResult) =
  match res with
  | Success (Some { MatchState.endIndex = i; MatchState.captures = captures; MatchState.input = input }) -> 
    Printf.printf "Matched %d characters ([%d-%d]) in '%s' (length=%d)\n" (i - at) at i sinput (List.length input);
    let f id = 
      match List.nth captures (id - 1) with
      | None ->
          Printf.printf "Group %d: undefined\n" id
      | Some { CaptureRange.startIndex = s; CaptureRange.endIndex = e } ->
          Printf.printf "Group %d: '%s' ([%d-%d])\n" id (from_list (drop s (take e input))) s e
    in
    List.iter f (Extracted.List.Range.Nat.Length.range 1 (List.length captures))

  | Success None -> Printf.printf "No match on '%s' \n" sinput

  | Failure OutOfFuel -> Printf.printf "Out of fuel on '%s' \n" sinput

  | Failure AssertionFailed -> Printf.printf "Assertion error during matching on '%s' \n" sinput

let test_regex_using_record regex input at rer =
  match Extracted.Semantics.compilePattern regex rer with
  | Success matcher ->
    let ls_input = to_list input in
    pretty_print_result input at (matcher ls_input at)
    
  | Failure AssertionFailed -> Printf.printf "Assertion error during compilation \n"


let test_regex regex input at ?(ignoreCase=false) ?(multiline=false) ?(dotAll=false) ?(unicode=false) () =
  let groups = (Extracted.StaticSemantics.countLeftCapturingParensWithin regex []) in
  let rer = {
    RegExp.ignoreCase = ignoreCase;
    RegExp.multiline = multiline;
    RegExp.dotAll = dotAll;
    RegExp.unicode = unicode;
    RegExp.capturingGroupsCount = groups;
  } in
  test_regex_using_record regex input at rer

let compare_regexes_using_record regex1 regex2 input at rer =
  match Extracted.Semantics.compilePattern regex1 rer, Extracted.Semantics.compilePattern regex2 rer with
  | Success m1, Success m2 ->
    let ls_input = to_list input in
    let res1 = (m1 ls_input at) in
    let res2 = (m2 ls_input at) in
    if res1 = res2 then
      (Printf.printf "The two regexes resulted in identical matches.\n";
      pretty_print_result input at res1)
    else
      (Printf.printf "The two regexes resulted in different matches.\n";
      pretty_print_result input at res1;
      pretty_print_result input at res2)
    
  | Failure AssertionFailed, _ -> Printf.printf "Assertion error during compilation \n"
  | _, Failure AssertionFailed -> Printf.printf "Assertion error during compilation \n"

let compare_regexes r1 r2 input at ?(ignoreCase=false) ?(multiline=false) ?(dotAll=false) ?(unicode=false) () =
  let groups = (Extracted.StaticSemantics.countLeftCapturingParensWithin r1 []) in
  let rer = {
    RegExp.ignoreCase = ignoreCase;
    RegExp.multiline = multiline;
    RegExp.dotAll = dotAll;
    RegExp.unicode = unicode;
    RegExp.capturingGroupsCount = groups;
  } in
  compare_regexes_using_record r1 r2 input at rer