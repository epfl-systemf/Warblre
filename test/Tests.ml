open! Warblre.Extracted.Patterns
open Warblre.Helpers
open Warblre.Notations

let%expect_test "sequence" =
  test_regex
    ((char 'a') -- (char 'b') -- (char 'b'))
    "abbb"
    0;
  [%expect {| Matched 3 characters ([0-3]) in 'abbb' (length=4) |}]


let%expect_test "greedy_star" = 
  test_regex
    (!* (char 'a'))
    "aaaaa"
    0;
  [%expect {| Matched 5 characters ([0-5]) in 'aaaaa' (length=5) |}]


let%expect_test "lazy_star_0" = 
  test_regex
    (!*? (char 'a'))
    "aaaaa"
    0;
  [%expect {| Matched 0 characters ([0-0]) in 'aaaaa' (length=5) |}]

let%expect_test "lazy_star_1" = 
  test_regex
    (!*? (char 'a') -- (char 'b'))
    "aaaaab"
    0;
  [%expect {| Matched 6 characters ([0-6]) in 'aaaaab' (length=6) |}]


let%expect_test "capture_reset" =
  test_regex
    !*(   group (1, char 'a')
    ||  group (2, char 'b'))
    "ab"
    0;
  [%expect {|
    Matched 2 characters ([0-2]) in 'ab' (length=2)
    Group 1: undefined
    Group 2: 'b' ([1-2]) |}]


let%expect_test "lookahead_0_pos" =
  test_regex
    (char 'a' -- (?= (char 'b')))
    "ab"
    0;
  [%expect {| Matched 1 characters ([0-1]) in 'ab' (length=2) |}]

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
  [%expect {| Matched 1 characters ([1-2]) in 'ab' (length=2) |}]

let%expect_test "lookbehind_0_neg_0" =
  test_regex
    ((?<= (char 'a')) -- char 'b')
    "b"
    0;
  [%expect {| No match on 'b' |}]

let%expect_test "lookbehind_0_neg_1" =
  test_regex
    ((?<= (char 'a')) -- char 'b')
    "bb"
    1;
  [%expect {| No match on 'bb' |}]



let%expect_test "neglookahead_0_pos_0" =
  test_regex
    (char 'a' -- (?! (char 'b')))
    "aa"
    0;
  [%expect {| Matched 1 characters ([0-1]) in 'aa' (length=2) |}]

let%expect_test "neglookahead_0_pos_1" =
  test_regex
    (char 'a' -- (?! (char 'b')))
    "a"
    0;
  [%expect {| Matched 1 characters ([0-1]) in 'a' (length=1) |}]

let%expect_test "neglookahead_0_neg" =
  test_regex
    (char 'a' -- (?! (char 'b')))
    "ab"
    0;
  [%expect {| No match on 'ab' |}]


let%expect_test "neglookbehind_0_pos_0" =
  test_regex
    ((?<! (char 'a')) -- char 'b')
    "bb"
    1;
  [%expect {| Matched 1 characters ([1-2]) in 'bb' (length=2) |}]

let%expect_test "neglookbehind_0_pos_1" =
  test_regex
    ((?<! (char 'a')) -- char 'b')
    "b"
    0;
  [%expect {| Matched 1 characters ([0-1]) in 'b' (length=1) |}]

let%expect_test "neglookbehind_0_neg" =
  test_regex
    ((?<! (char 'a')) -- char 'b')
    "ab"
    1;
  [%expect {| No match on 'ab' |}]

let%expect_test "backref_0_pos" =
  test_regex
    (group (0, (char 'a')) -- !$ 0)
    "aa"
    0;
  [%expect {|
    Matched 2 characters ([0-2]) in 'aa' (length=2)
    Group 0: 'a' ([0-1]) |}]

let%expect_test "backref_0_neg_0" =
  test_regex
    (group (0, (char 'a')) -- !$ 0)
    "ab"
    0;
  [%expect {| No match on 'ab' |}]

let%expect_test "backref_0_neg_1" =
  test_regex
    (group (0, (char 'a')) -- !$ 0)
    "a"
    0;
  [%expect {| No match on 'a' |}]

let%expect_test "backref_undefined" =
  test_regex
    ((group (0, (char 'a')) || group (1, (char 'b'))) -- !$ 1)
    "aa"
    0;
  [%expect {|
    Matched 1 characters ([0-1]) in 'aa' (length=2)
    Group 0: 'a' ([0-1])
    Group 1: undefined |}]

let%expect_test "backref_multiple" =
  test_regex
    (group (0, (char 'a')) -- !$ 0 -- !$ 1 -- group (1, (char 'b')) -- !$ 0 -- !$ 1)
    "aabab"
    0;
  [%expect {|
    Matched 5 characters ([0-5]) in 'aabab' (length=5)
    Group 0: 'a' ([0-1])
    Group 1: 'b' ([2-3]) |}]

let%expect_test "backref_long_pos" =
  test_regex
    (group (0, (char 'a') -- (char 'b') -- (char 'a')) -- !$ 0)
    "abaaba"
    0;
  [%expect {|
    Matched 6 characters ([0-6]) in 'abaaba' (length=6)
    Group 0: 'aba' ([0-3]) |}]

let%expect_test "backref_long_neg_0" =
  test_regex
    (group (0, (char 'a') -- (char 'b') -- (char 'a')) -- !$ 0)
    "abaab"
    0;
  [%expect {| No match on 'abaab' |}]

let%expect_test "backref_long_neg_1" =
test_regex
  (group (0, (char 'a') -- (char 'b') -- (char 'a')) -- !$ 0)
  "abacba"
  0;
[%expect {| No match on 'abacba' |}]

let%expect_test "backref_long_neg_2" =
  test_regex
    (group (0, (char 'a') -- (char 'b') -- (char 'a')) -- !$ 0)
    "abaaca"
    0;
  [%expect {| No match on 'abaaca' |}]

let%expect_test "backref_long_neg_3" =
  test_regex
    (group (0, (char 'a') -- (char 'b') -- (char 'a')) -- !$ 0)
    "abaabc"
    0;
  [%expect {| No match on 'abaabc' |}]