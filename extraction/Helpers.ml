open Extracted
open Notation

let rec drop n ls = match n with
  | O -> ls
  | S n' -> match ls with
    | _ :: ls' -> drop n' ls'
    | [] -> []

let rec take n ls = match n with
  | O -> []
  | S n' -> match ls with
    | h :: ls' -> h :: (take n' ls')
    | [] -> []

let to_list s = List.init (String.length s) (String.get s)
let from_list ls = String.init (List.length ls) (List.nth ls)

let rec to_nat i = if i > 0 then S (to_nat (i-1)) else O

let rec from_nat i = match i with
  | O -> 0
  | S n -> (from_nat n) + 1

(* let rec (-) l r = match r with
  | O -> l
  | S r' -> match l with
    | O -> O
    | S l' -> l' - r' *)

let test_regex regex input =
  let matcher = Semantics.compilePattern regex in
  let ls_input = to_list input in

  match matcher ls_input (to_nat 0) with

  | Success { MatchState.endIndex = i; MatchState.captures = captures; _ } -> 
    Printf.printf "Matched %d characters in '%s' (length=%d)\n" (from_nat i) input (from_nat (length ls_input));
    let f name = 
      match Interop.Ocaml_Map_Int.find_opt name captures with
      | None ->
          Printf.printf "Group %d: undefined\n" name
      | Some { CaptureRange.startIndex = s; CaptureRange.endIndex = e } ->
          Printf.printf "Group %d: '%s' (%d-%d)\n" name (from_list (drop s (take e ls_input))) (from_nat s) (from_nat e)
    in
    Interop.Ocaml_Set_Int.iter f (Extracted.StaticSemantics.capturingGroupsWithin regex)

  | Failure Mismatch -> Printf.printf "No match on '%s' \n" input

  | Failure OutOfFuel -> Printf.printf "Out of fuel on '%s' \n" input

  | Failure AssertionFailed -> Printf.printf "Assertion error on '%s' \n" input