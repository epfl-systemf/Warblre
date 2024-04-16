open Warblre.Notations.UnicodeNotations
open Warblre.Testing.UnicodeTester

let%expect_test "ascii" =
  test_regex
    (!* (uprop "Alphabetic"))
    "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ"
    0 ();
  [%expect{| /\p{...}*/ matched 52 characters ([0-52]) in 'abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ' (length=52) |}]

let%expect_test "space" =
  test_regex
    (!* (uprop "Alphabetic"))
    "abcdefghijklmno pqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ"
    0 ();
  [%expect{| /\p{...}*/ matched 15 characters ([0-15]) in 'abcdefghijklmno pqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ' (length=53) |}]

let%expect_test "tab" =
  test_regex
    (!* (uprop "Alphabetic"))
    "abcdefghijklmno\tpqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ"
    0 ();
  [%expect{| /\p{...}*/ matched 15 characters ([0-15]) in 'abcdefghijklmno	pqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ' (length=53) |}]

let%expect_test "greek" =
  test_regex
    (!* (uprop "Alphabetic"))
    "αβγδεϝͷϛζͱηθιϳκλμνξοπϻϟϙρσͼτυφχψωϡͳϸ"
    0 ();
  [%expect{| /\p{...}*/ matched 36 characters ([0-36]) in 'αβγδεϝͷϛζͱηθιϳκλμνξοπϻϟϙρσͼτυφχψωϡͳϸ' (length=36) |}]