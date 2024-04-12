open Warblre.Notations.UnicodeNotations
open Warblre.Testing.UnicodeTester

let%expect_test "backref_0_pos" =
  test_regex
    (group ((cchar 'a')) -- !$ 1)
    "aa"
    0 ();
  [%expect {|
    Matched 2 characters ([0-2]) in 'aa' (length=2)
    Group 1: 'a' ([0-1]) |}]

let%expect_test "backref_0_neg_0" =
  test_regex
    (group ((cchar 'a')) -- !$ 1)
    "ab"
    0 ();
  [%expect {| No match on 'ab' |}]

let%expect_test "backref_0_neg_1" =
  test_regex
    (group ((cchar 'a')) -- !$ 1)
    "a"
    0 ();
  [%expect {| No match on 'a' |}]

let%expect_test "backref_undefined" =
  test_regex
    ((group ((cchar 'a')) || group ((cchar 'b'))) -- !$ 2)
    "aa"
    0 ();
  [%expect {|
    Matched 1 characters ([0-1]) in 'aa' (length=2)
    Group 1: 'a' ([0-1])
    Group 2: undefined |}]

let%expect_test "backref_multiple" =
  test_regex
    (group ((cchar 'a')) -- !$ 1 -- !$ 2 -- group ((cchar 'b')) -- !$ 1 -- !$ 2)
    "aabab"
    0 ();
  [%expect {|
    Matched 5 characters ([0-5]) in 'aabab' (length=5)
    Group 1: 'a' ([0-1])
    Group 2: 'b' ([2-3]) |}]

let%expect_test "backref_long_pos" =
  test_regex
    (group ((cchar 'a') -- (cchar 'b') -- (cchar 'a')) -- !$ 1)
    "abaaba"
    0 ();
  [%expect {|
    Matched 6 characters ([0-6]) in 'abaaba' (length=6)
    Group 1: 'aba' ([0-3]) |}]

let%expect_test "backref_long_neg_0" =
  test_regex
    (group ((cchar 'a') -- (cchar 'b') -- (cchar 'a')) -- !$ 1)
    "abaab"
    0 ();
  [%expect {| No match on 'abaab' |}]

let%expect_test "backref_long_neg_1" =
test_regex
  (group ((cchar 'a') -- (cchar 'b') -- (cchar 'a')) -- !$ 1)
  "abacba"
  0 ();
[%expect {| No match on 'abacba' |}]

let%expect_test "backref_long_neg_2" =
  test_regex
    (group ((cchar 'a') -- (cchar 'b') -- (cchar 'a')) -- !$ 1)
    "abaaca"
    0 ();
  [%expect {| No match on 'abaaca' |}]

let%expect_test "backref_long_neg_3" =
  test_regex
    (group ((cchar 'a') -- (cchar 'b') -- (cchar 'a')) -- !$ 1)
    "abaabc"
    0 ();
  [%expect {| No match on 'abaabc' |}]



  
let%expect_test "named_backref_0_0" =
test_regex
    (ngroup ("G", (cchar 'a')) -- !$ 1)
    "aa"
    0 ();
  [%expect {|
  Matched 2 characters ([0-2]) in 'aa' (length=2)
  Group 1: 'a' ([0-1]) |}]

let%expect_test "named_backref_0_1" =
    test_regex
      (ngroup ("G", (cchar 'a')) -- !& "G")
      "aa"
      0 ();
    [%expect {|
      Matched 2 characters ([0-2]) in 'aa' (length=2)
      Group 1: 'a' ([0-1]) |}]
  
let%expect_test "named_backref_1_0" =
  test_regex
    (
      ngroup ("G", (cchar 'a')) -- 
      ngroup ("H", (cchar 'b')) -- 
      ngroup ("I", (cchar 'c')) -- 
      !& "G"
    )
    "abca"
    0 ();
  [%expect {|
    Matched 4 characters ([0-4]) in 'abca' (length=4)
    Group 1: 'a' ([0-1])
    Group 2: 'b' ([1-2])
    Group 3: 'c' ([2-3]) |}]
  
let%expect_test "named_backref_1_1" =
  test_regex
    (
      ngroup ("G", (cchar 'a')) -- 
      ngroup ("H", (cchar 'b')) -- 
      ngroup ("I", (cchar 'c')) -- 
      !& "H"
    )
    "abcb"
    0 ();
  [%expect {|
    Matched 4 characters ([0-4]) in 'abcb' (length=4)
    Group 1: 'a' ([0-1])
    Group 2: 'b' ([1-2])
    Group 3: 'c' ([2-3]) |}]
  
let%expect_test "named_backref_1_2" =
  test_regex
    (
      ngroup ("G", (cchar 'a')) -- 
      ngroup ("H", (cchar 'b')) -- 
      ngroup ("I", (cchar 'c')) -- 
      !& "I"
    )
    "abcc"
    0 ();
  [%expect {|
    Matched 4 characters ([0-4]) in 'abcc' (length=4)
    Group 1: 'a' ([0-1])
    Group 2: 'b' ([1-2])
    Group 3: 'c' ([2-3]) |}]
  
let%expect_test "named_backref_nested" =
  test_regex
    (
      ngroup ("G", 
        (cchar 'a') -- 
        ngroup ("H", 
          (cchar 'b') -- 
          ngroup ("I", (cchar 'c')))) -- 
      !& "I" -- !& "H" -- !& "G"
    )
    "abccbcabc"
    0 ();
  [%expect {|
    Matched 9 characters ([0-9]) in 'abccbcabc' (length=9)
    Group 1: 'abc' ([0-3])
    Group 2: 'bc' ([1-3])
    Group 3: 'c' ([2-3]) |}]