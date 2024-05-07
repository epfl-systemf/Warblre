open Warblre_ocaml.OCamlEngines.UnicodeNotations
open Warblre_ocaml.OCamlEngines.UnicodeTester

let%expect_test "ascii" =
  test_regex
    (!* (uprop "Alphabetic"))
    "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ"
    0 ();
  [%expect{|
    Regex /\p{...}*/ on 'abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ' at 0:
    Input: abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ
    End: 52
    Captures:
    	None |}]

let%expect_test "space" =
  test_regex
    (!* (uprop "Alphabetic"))
    "abcdefghijklmno pqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ"
    0 ();
  [%expect{|
    Regex /\p{...}*/ on 'abcdefghijklmno pqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ' at 0:
    Input: abcdefghijklmno pqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ
    End: 15
    Captures:
    	None |}]

let%expect_test "tab" =
  test_regex
    (!* (uprop "Alphabetic"))
    "abcdefghijklmno\tpqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ"
    0 ();
  [%expect{|
    Regex /\p{...}*/ on 'abcdefghijklmno	pqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ' at 0:
    Input: abcdefghijklmno	pqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ
    End: 15
    Captures:
    	None |}]

let%expect_test "greek" =
  test_regex
    (!* (uprop "Alphabetic"))
    "αβγδεϝͷϛζͱηθιϳκλμνξοπϻϟϙρσͼτυφχψωϡͳϸ"
    0 ();
  [%expect{|
    Regex /\p{...}*/ on 'αβγδεϝͷϛζͱηθιϳκλμνξοπϻϟϙρσͼτυφχψωϡͳϸ' at 0:
    Input: αβγδεϝͷϛζͱηθιϳκλμνξοπϻϟϙρσͼτυφχψωϡͳϸ
    End: 36
    Captures:
    	None |}]