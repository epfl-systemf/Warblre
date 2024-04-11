open Extracted.Notation
open Extracted.ECMA_u

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

(* Retrieves a substring. The unicode argument specifies whether the range [s..e]
   should be interpreted as a range of UTF16 code units or as a range of Unicode code points. *)
let substring str s e unicode: string =
  let b = Buffer.create (String.length str) in
  let rec iter i rem: unit =
    if rem = 0 then ()
    else
      let u = StringLabels.get_utf_8_uchar str i in
      if Uchar.utf_decode_is_valid u then (
        Buffer.add_utf_8_uchar b (Uchar.utf_decode_uchar u);
        iter (i+1) (rem-1))
      else (
        if unicode
        then iter (i+1) rem
        else  iter (i+1) (rem-1))
  in
  iter s (e-s);
  Buffer.contents b

let pretty_print_result sinput at (res: coq_MatchResult) unicode =
  match res with
  | Success (Some { MatchState.endIndex = i; MatchState.captures = captures; MatchState.input = input }) -> 
    Printf.printf "Matched %d characters ([%d-%d]) in '%s' (length=%d)\n" (i - at) at i sinput (List.length input);
    let f id = 
      match List.nth captures (id - 1) with
      | None ->
          Printf.printf "Group %d: undefined\n" id
      | Some { CaptureRange.startIndex = s; CaptureRange.endIndex = e } ->
          Printf.printf "Group %d: '%s' ([%d-%d])\n" id (substring sinput s e unicode) s e
    in
    List.iter f (Extracted.List.Range.Nat.Length.range 1 (List.length captures))

  | Success None -> Printf.printf "No match on '%s' \n" sinput

  | Failure OutOfFuel -> Printf.printf "Out of fuel on '%s' \n" sinput

  | Failure AssertionFailed -> Printf.printf "Assertion error during matching on '%s' \n" sinput

let test_regex_using_record regex input at rer =
  match compilePattern regex rer with
  | Success matcher ->
    let ls_input = Interop.Utf16.string_to_utf16 input in
    pretty_print_result input at (matcher (Obj.magic ls_input) at) (Extracted.RegExpRecord.unicode rer)
    
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
    let ls_input = Interop.Unicode.string_to_utf8 input in
    let res1 = (m1 (Obj.magic ls_input) at) in
    let res2 = (m2 (Obj.magic ls_input) at) in
    if res1 = res2 then
      (Printf.printf "The two regexes resulted in identical matches.\n";
      pretty_print_result input at res1 (Extracted.RegExpRecord.unicode rer))
    else
      (Printf.printf "The two regexes resulted in different matches.\n";
      pretty_print_result input at res1 (Extracted.RegExpRecord.unicode rer);
      pretty_print_result input at res2 (Extracted.RegExpRecord.unicode rer))

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