open Extracted
open Notation

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

let test_regex regex input =
  let matcher = Semantics.compilePattern regex in
  let ls_input = to_list input in

  match matcher ls_input 0 with

  | Success (Some { MatchState.endIndex = i; MatchState.captures = captures; _ }) -> 
    Printf.printf "Matched %d characters in '%s' (length=%d)\n" i input (length ls_input);
    let f name = 
      match Interop.Ocaml_Map_Int.find_opt name captures with
      | None ->
          Printf.printf "Group %d: undefined\n" name
      | Some { CaptureRange.startIndex = s; CaptureRange.endIndex = e } ->
          Printf.printf "Group %d: '%s' (%d-%d)\n" name (from_list (drop s (take e ls_input))) s e
    in
    Interop.Ocaml_Set_Int.iter f (Extracted.StaticSemantics.capturingGroupsWithin regex)

  | Success None -> Printf.printf "No match on '%s' \n" input

  | Failure OutOfFuel -> Printf.printf "Out of fuel on '%s' \n" input

  | Failure AssertionFailed -> Printf.printf "Assertion error on '%s' \n" input