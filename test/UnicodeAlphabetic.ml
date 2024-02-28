open! Warblre.Extracted.Patterns
open Warblre.Helpers
open Warblre.Notations

let%expect_test "ascii" =
  test_regex
    (!* (uprop "Alphabetic"))
    "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ"
    0 ();
  [%expect {| Matched 52 characters ([0-52]) in 'abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ' (length=52) |}]

let%expect_test "space" =
  test_regex
    (!* (uprop "Alphabetic"))
    "abcdefghijklmno pqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ"
    0 ();
  [%expect {| Matched 15 characters ([0-15]) in 'abcdefghijklmno pqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ' (length=53) |}]

let%expect_test "tab" =
  test_regex
    (!* (uprop "Alphabetic"))
    "abcdefghijklmno\tpqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ"
    0 ();
  [%expect {| Matched 15 characters ([0-15]) in 'abcdefghijklmno	pqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ' (length=53) |}]

let%expect_test "greek" =
  test_regex
    (!* (uprop "Alphabetic"))
    "αβγδεϝͷϛζͱηθιϳκλμνξοπϻϟϙρσͼτυφχψωϡͳϸ"
    0 ();
  [%expect {| Matched 36 characters ([0-36]) in 'αβγδεϝͷϛζͱηθιϳκλμνξοπϻϟϙρσͼτυφχψωϡͳϸ' (length=36) |}]