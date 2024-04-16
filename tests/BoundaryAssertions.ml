open Warblre.Notations.UnicodeNotations
open Warblre.Testing.UnicodeTester

let%expect_test "match_start_pos" =
  test_regex
    (InputStart -- cchar 'a')
    "aa"
    0 ();
  [%expect {| /^a/ matched 1 characters ([0-1]) in 'aa' (length=2) |}]

let%expect_test "match_start_neg_0" =
  test_regex
    (InputStart -- cchar 'a')
    "aa"
    1 ();
  [%expect {| /^a/ matched nothing on 'aa' |}]

let%expect_test "match_start_neg_1" =
  test_regex
    ((cchar 'a') -- InputStart -- (cchar 'a'))
    "aa"
    0 ();
  [%expect {| /a^a/ matched nothing on 'aa' |}]



let%expect_test "match_end_pos" =
  test_regex
    ((cchar 'a') -- InputEnd)
    "aa"
    1 ();
  [%expect {| /a$/ matched 1 characters ([1-2]) in 'aa' (length=2) |}]

let%expect_test "match_start_neg_0" =
  test_regex
  ((cchar 'a') -- InputEnd)
    "aa"
    0 ();
  [%expect {| /a$/ matched nothing on 'aa' |}]

let%expect_test "match_start_neg_1" =
  test_regex
    ((cchar 'a') -- InputEnd -- (cchar 'a'))
    "aa"
    0 ();
  [%expect {| /a$a/ matched nothing on 'aa' |}]



  let%expect_test "word_boundary_pos" =
  test_regex
    ((cchar 'a') -- WordBoundary -- (cchar ' '))
    "a a"
    0 ();
  [%expect {| /a\b / matched 2 characters ([0-2]) in 'a a' (length=3) |}]

let%expect_test "word_boundary_neg" =
  test_regex
    ((cchar 'a') -- WordBoundary -- (cchar 'a'))
    "aaa"
    0 ();
  [%expect {| /a\ba/ matched nothing on 'aaa' |}]



let%expect_test "not_word_boundary_pos" =
  test_regex
    ((cchar 'a') -- NotWordBoundary -- (cchar 'a'))
    "aaa"
    0 ();
  [%expect {| /a\Ba/ matched 2 characters ([0-2]) in 'aaa' (length=3) |}]

let%expect_test "not_word_boundary_neg" =
  test_regex
    ((cchar 'a') -- NotWordBoundary -- (cchar ' '))
    "a a"
    0 ();
  [%expect {| /a\B / matched nothing on 'a a' |}]
