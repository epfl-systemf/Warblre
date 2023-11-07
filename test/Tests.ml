open! Warblre.Extracted.Patterns
open Warblre.Helpers
open Warblre.Notations

let%expect_test "sequence" =
  test_regex
    ((char 'a') -- (char 'b') -- (char 'b'))
    "abbb"
    0;
  [%expect {| Matched 3 characters in 'abbb' (length=4) |}]


let%expect_test "greedy_star" = 
  test_regex
    (!* (char 'a'))
    "aaaaa"
    0;
  [%expect {| Matched 5 characters in 'aaaaa' (length=5) |}]


let%expect_test "lazy_star_0" = 
  test_regex
    (!*? (char 'a'))
    "aaaaa"
    0;
  [%expect {| Matched 0 characters in 'aaaaa' (length=5) |}]

let%expect_test "lazy_star_1" = 
  test_regex
    (!*? (char 'a') -- (char 'b'))
    "aaaaab"
    0;
  [%expect {| Matched 6 characters in 'aaaaab' (length=6) |}]


let%expect_test "capture_reset" =
  test_regex
    !*(   group (1, char 'a')
    ||  group (2, char 'b'))
    "ab"
    0;
  [%expect {|
    Matched 2 characters in 'ab' (length=2)
    Group 1: undefined
    Group 2: 'b' (1-2) |}]


let%expect_test "lookahead_0_pos" =
  test_regex
    (char 'a' -- (?= (char 'b')))
    "ab"
    0;
  [%expect {| Matched 1 characters in 'ab' (length=2) |}]

let%expect_test "lookahead_0_neg_0" =
  test_regex
    (char 'a' -- (?= (char 'b')))
    "a"
    0;
  [%expect {| No match on 'a' |}]

let%expect_test "lookahead_0_neg_1" =
  test_regex
    (char 'a' -- (?= (char 'b')))
    "aa"
    0;
  [%expect {| No match on 'aa' |}]


let%expect_test "lookbehind_0_pos" =
  test_regex
    ((?<= (char 'a')) -- char 'b')
    "ab"
    1;
  [%expect {|  |}]

let%expect_test "lookbehind_0_neg_0" =
  test_regex
    ((?<= (char 'a')) -- char 'b')
    "b"
    1;
  [%expect {|  |}]

let%expect_test "lookbehind_0_neg_1" =
  test_regex
    ((?<= (char 'a')) -- char 'b')
    "bb"
    1;
  [%expect {|  |}]