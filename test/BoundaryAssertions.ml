open! Warblre.Extracted.Patterns
open Warblre.Helpers
open Warblre.Notations

let%expect_test "match_start_pos" =
  test_regex
    (InputStart -- char 'a')
    "aa"
    0 ();
  [%expect {| Matched 1 characters ([0-1]) in 'aa' (length=2) |}]

let%expect_test "match_start_neg_0" =
  test_regex
    (InputStart -- char 'a')
    "aa"
    1 ();
  [%expect {| No match on 'aa' |}]

let%expect_test "match_start_neg_1" =
  test_regex
    ((char 'a') -- InputStart -- (char 'a'))
    "aa"
    0 ();
  [%expect {| No match on 'aa' |}]



let%expect_test "match_end_pos" =
  test_regex
    ((char 'a') -- InputEnd)
    "aa"
    1 ();
  [%expect {| Matched 1 characters ([1-2]) in 'aa' (length=2) |}]

let%expect_test "match_start_neg_0" =
  test_regex
  ((char 'a') -- InputEnd)
    "aa"
    0 ();
  [%expect {| No match on 'aa' |}]

let%expect_test "match_start_neg_1" =
  test_regex
    ((char 'a') -- InputEnd -- (char 'a'))
    "aa"
    0 ();
  [%expect {| No match on 'aa' |}]



  let%expect_test "word_boundary_pos" =
  test_regex
    ((char 'a') -- WordBoundary -- (char ' '))
    "a a"
    0 ();
  [%expect {| Matched 2 characters ([0-2]) in 'a a' (length=3) |}]

let%expect_test "word_boundary_neg" =
  test_regex
    ((char 'a') -- WordBoundary -- (char 'a'))
    "aaa"
    0 ();
  [%expect {| No match on 'aaa' |}]



let%expect_test "not_word_boundary_pos" =
  test_regex
    ((char 'a') -- NotWordBoundary -- (char 'a'))
    "aaa"
    0 ();
  [%expect {| Matched 2 characters ([0-2]) in 'aaa' (length=3) |}]

let%expect_test "not_word_boundary_neg" =
  test_regex
    ((char 'a') -- NotWordBoundary -- (char ' '))
    "a a"
    0 ();
  [%expect {| No match on 'a a' |}]
