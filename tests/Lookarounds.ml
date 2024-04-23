open Warblre.Notations.UnicodeNotations
open Warblre.Testing.UnicodeTester

let%expect_test "lookahead_0_pos" =
  test_regex
    (cchar 'a' -- (?= (cchar 'b')))
    "ab"
    0 ();
  [%expect {| Matched 1 characters ([0-1]) in 'ab' (length=2) |}]

let%expect_test "lookahead_0_neg_0" =
  test_regex
    (cchar 'a' -- (?= (cchar 'b')))
    "a"
    0 ();
  [%expect {| No match on 'a' |}]

let%expect_test "lookahead_0_neg_1" =
  test_regex
    (cchar 'a' -- (?= (cchar 'b')))
    "aa"
    0 ();
  [%expect {| No match on 'aa' |}]


let%expect_test "lookbehind_0_pos" =
  test_regex
    ((?<= (cchar 'a')) -- cchar 'b')
    "ab"
    1 ();
  [%expect {| Matched 1 characters ([1-2]) in 'ab' (length=2) |}]

let%expect_test "lookbehind_0_neg_0" =
  test_regex
    ((?<= (cchar 'a')) -- cchar 'b')
    "b"
    0 ();
  [%expect {| No match on 'b' |}]

let%expect_test "lookbehind_0_neg_1" =
  test_regex
    ((?<= (cchar 'a')) -- cchar 'b')
    "bb"
    1 ();
  [%expect {| No match on 'bb' |}]



let%expect_test "neglookahead_0_pos_0" =
  test_regex
    (cchar 'a' -- (?! (cchar 'b')))
    "aa"
    0 ();
  [%expect {| Matched 1 characters ([0-1]) in 'aa' (length=2) |}]

let%expect_test "neglookahead_0_pos_1" =
  test_regex
    (cchar 'a' -- (?! (cchar 'b')))
    "a"
    0 ();
  [%expect {| Matched 1 characters ([0-1]) in 'a' (length=1) |}]

let%expect_test "neglookahead_0_neg" =
  test_regex
    (cchar 'a' -- (?! (cchar 'b')))
    "ab"
    0 ();
  [%expect {| No match on 'ab' |}]


let%expect_test "neglookbehind_0_pos_0" =
  test_regex
    ((?<! (cchar 'a')) -- cchar 'b')
    "bb"
    1 ();
  [%expect {| Matched 1 characters ([1-2]) in 'bb' (length=2) |}]

let%expect_test "neglookbehind_0_pos_1" =
  test_regex
    ((?<! (cchar 'a')) -- cchar 'b')
    "b"
    0 ();
  [%expect {| Matched 1 characters ([0-1]) in 'b' (length=1) |}]

let%expect_test "neglookbehind_0_neg" =
  test_regex
    ((?<! (cchar 'a')) -- cchar 'b')
    "ab"
    1 ();
  [%expect {| No match on 'ab' |}]


(* Note: using [^]  would be better than . *)
let%expect_test "lookbehind_anchor_emulation_pos_0" =
  test_regex
    ((?<! (Dot)) -- !*(cchar 'b'))
    "bbbb"
    0 ();
  [%expect {| Matched 4 characters ([0-4]) in 'bbbb' (length=4) |}]

  let%expect_test "lookbehind_anchor_emulation_neg_0" =
  test_regex
    ((?<! (Dot)) -- !*(cchar 'b'))
    "bbbb"
    1 ();
  [%expect {| No match on 'bbbb' |}]

let%expect_test "lookbehind_anchor_emulation_neg_1" =
  test_regex
    ((?<! (Dot)) -- !*(cchar 'b'))
    "abbbb"
    1 ();
  [%expect {| No match on 'abbbb' |}]

let%expect_test "lookahead_anchor_emulation_pos_0" =
  test_regex
    (!*(cchar 'b') -- (?! (Dot)))
    "bbbb"
    0 ();
  [%expect {| Matched 4 characters ([0-4]) in 'bbbb' (length=4) |}]

let%expect_test "lookbehind_anchor_emulation_neg_0" =
  test_regex
    (!*(cchar 'b') -- (?! (Dot)))
    "bbbba"
    0 ();
  [%expect {| No match on 'bbbba' |}]