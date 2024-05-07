open Warblre_ocaml.OCamlEngines.UnicodeNotations
open Warblre_ocaml.OCamlEngines.UnicodePrinter

let pp r = Printf.printf "%s\n" (regex_to_string ~strict:true r)

let%expect_test "printer_or_assoc_0" =
  pp (Disjunction (char "a", Disjunction (char "b", char "c")));
  [%expect {| /a|b|c/ |}]

let%expect_test "printer_or_assoc_1" =
  pp (Disjunction (Disjunction (char "a", char "b"), char "c"));
  [%expect {| /(?:a|b)|c/ |}]

let%expect_test "printer_or_seq_0" =
  pp (Disjunction (char "a" -- char "b", char "c" -- char "d"));
  [%expect {| /ab|cd/ |}]

let%expect_test "printer_or_seq_1" =
  pp (Disjunction (char "a", char "b") -- Disjunction (char "c", char "d"));
  [%expect {| /(?:a|b)(?:c|d)/ |}]
    
let%expect_test "printer_seq_quant_0" =
  pp (!* (char "a") -- !* (char "b"));
  [%expect {| /a*b*/ |}]
  
let%expect_test "printer_seq_quant_0" =
  pp (!* (char "a" --  char "b"));
  [%expect {| /(?:ab)*/ |}]

let%expect_test "special_chars" =
  pp (List.fold_right (fun c r -> cchar c -- r) ('\\' :: '/' :: '-' :: '[' :: ']' :: '{' :: '}' :: '(' :: ')' :: '*' :: '+' :: '?' :: '$' :: '^' :: '|' :: '.' :: []) Empty);
  [%expect {| /\\\/\-\[\]\{\}\(\)\*\+\?\$\^\|\./ |}]