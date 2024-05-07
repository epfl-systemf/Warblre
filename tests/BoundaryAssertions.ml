open Warblre_ocaml.OCamlEngines.UnicodeNotations
open Warblre_ocaml.OCamlEngines.UnicodeTester

let%expect_test "match_start_pos" =
  test_regex
    (InputStart -- cchar 'a')
    "aa"
    0 ();
  [%expect {|
    Regex /^a/ on 'aa' at 0:
    Input: aa
    End: 1
    Captures:
    	None |}]

let%expect_test "match_start_neg_0" =
  test_regex
    (InputStart -- cchar 'a')
    "aa"
    1 ();
  [%expect {|
    Regex /^a/ on 'aa' at 1:
    No match |}]

let%expect_test "match_start_neg_1" =
  test_regex
    ((cchar 'a') -- InputStart -- (cchar 'a'))
    "aa"
    0 ();
  [%expect {|
    Regex /a^a/ on 'aa' at 0:
    No match |}]



let%expect_test "match_end_pos" =
  test_regex
    ((cchar 'a') -- InputEnd)
    "aa"
    1 ();
  [%expect {|
    Regex /a$/ on 'aa' at 1:
    Input: aa
    End: 2
    Captures:
    	None |}]

let%expect_test "match_start_neg_0" =
  test_regex
  ((cchar 'a') -- InputEnd)
    "aa"
    0 ();
  [%expect {|
    Regex /a$/ on 'aa' at 0:
    No match |}]

let%expect_test "match_start_neg_1" =
  test_regex
    ((cchar 'a') -- InputEnd -- (cchar 'a'))
    "aa"
    0 ();
  [%expect {|
    Regex /a$a/ on 'aa' at 0:
    No match |}]



  let%expect_test "word_boundary_pos" =
  test_regex
    ((cchar 'a') -- WordBoundary -- (cchar ' '))
    "a a"
    0 ();
  [%expect {|
    Regex /a\b / on 'a a' at 0:
    Input: a a
    End: 2
    Captures:
    	None |}]

let%expect_test "word_boundary_neg" =
  test_regex
    ((cchar 'a') -- WordBoundary -- (cchar 'a'))
    "aaa"
    0 ();
  [%expect {|
    Regex /a\ba/ on 'aaa' at 0:
    No match |}]



let%expect_test "not_word_boundary_pos" =
  test_regex
    ((cchar 'a') -- NotWordBoundary -- (cchar 'a'))
    "aaa"
    0 ();
  [%expect {|
    Regex /a\Ba/ on 'aaa' at 0:
    Input: aaa
    End: 2
    Captures:
    	None |}]

let%expect_test "not_word_boundary_neg" =
  test_regex
    ((cchar 'a') -- NotWordBoundary -- (cchar ' '))
    "a a"
    0 ();
  [%expect {|
    Regex /a\B / on 'a a' at 0:
    No match |}]
