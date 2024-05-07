open Warblre_ocaml.OCamlEngines.UnicodeNotations
open Warblre_ocaml.OCamlEngines.UnicodeTester

let%expect_test "backref_0_pos" =
  test_regex
    (group ((cchar 'a')) -- !$ 1)
    "aa"
    0 ();
  [%expect {|
    Regex /(a)\1/ on 'aa' at 0:
    Input: aa
    End: 2
    Captures:
    	# 0 : (0,1) |}]

let%expect_test "backref_0_neg_0" =
  test_regex
    (group ((cchar 'a')) -- !$ 1)
    "ab"
    0 ();
  [%expect {|
    Regex /(a)\1/ on 'ab' at 0:
    No match |}]

let%expect_test "backref_0_neg_1" =
  test_regex
    (group ((cchar 'a')) -- !$ 1)
    "a"
    0 ();
  [%expect {|
    Regex /(a)\1/ on 'a' at 0:
    No match |}]

let%expect_test "backref_undefined" =
  test_regex
    ((group ((cchar 'a')) || group ((cchar 'b'))) -- !$ 2)
    "aa"
    0 ();
  [%expect {|
    Regex /(?:(a)|(b))\2/ on 'aa' at 0:
    Input: aa
    End: 1
    Captures:
    	# 0 : (0,1)
    	# 1 : Undefined |}]

let%expect_test "backref_multiple" =
  test_regex
    (group ((cchar 'a')) -- !$ 1 -- !$ 2 -- group ((cchar 'b')) -- !$ 1 -- !$ 2)
    "aabab"
    0 ();
  [%expect {|
    Regex /(a)\1\2(b)\1\2/ on 'aabab' at 0:
    Input: aabab
    End: 5
    Captures:
    	# 0 : (0,1)
    	# 1 : (2,3) |}]

let%expect_test "backref_long_pos" =
  test_regex
    (group ((cchar 'a') -- (cchar 'b') -- (cchar 'a')) -- !$ 1)
    "abaaba"
    0 ();
  [%expect {|
    Regex /(aba)\1/ on 'abaaba' at 0:
    Input: abaaba
    End: 6
    Captures:
    	# 0 : (0,3) |}]

let%expect_test "backref_long_neg_0" =
  test_regex
    (group ((cchar 'a') -- (cchar 'b') -- (cchar 'a')) -- !$ 1)
    "abaab"
    0 ();
  [%expect {|
    Regex /(aba)\1/ on 'abaab' at 0:
    No match |}]

let%expect_test "backref_long_neg_1" =
test_regex
  (group ((cchar 'a') -- (cchar 'b') -- (cchar 'a')) -- !$ 1)
  "abacba"
  0 ();
[%expect {|
  Regex /(aba)\1/ on 'abacba' at 0:
  No match |}]

let%expect_test "backref_long_neg_2" =
  test_regex
    (group ((cchar 'a') -- (cchar 'b') -- (cchar 'a')) -- !$ 1)
    "abaaca"
    0 ();
  [%expect {|
    Regex /(aba)\1/ on 'abaaca' at 0:
    No match |}]

let%expect_test "backref_long_neg_3" =
  test_regex
    (group ((cchar 'a') -- (cchar 'b') -- (cchar 'a')) -- !$ 1)
    "abaabc"
    0 ();
  [%expect {|
    Regex /(aba)\1/ on 'abaabc' at 0:
    No match |}]



  
let%expect_test "named_backref_0_0" =
test_regex
    (ngroup ("G", (cchar 'a')) -- !$ 1)
    "aa"
    0 ();
  [%expect {|
  Regex /(?<G>a)\1/ on 'aa' at 0:
  Input: aa
  End: 2
  Captures:
  	# 0 : (0,1) |}]

let%expect_test "named_backref_0_1" =
    test_regex
      (ngroup ("G", (cchar 'a')) -- !& "G")
      "aa"
      0 ();
    [%expect {|
      Regex /(?<G>a)\k<G>/ on 'aa' at 0:
      Input: aa
      End: 2
      Captures:
      	# 0 : (0,1) |}]
  
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
    Regex /(?<G>a)(?<H>b)(?<I>c)\k<G>/ on 'abca' at 0:
    Input: abca
    End: 4
    Captures:
    	# 0 : (0,1)
    	# 1 : (1,2)
    	# 2 : (2,3) |}]
  
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
    Regex /(?<G>a)(?<H>b)(?<I>c)\k<H>/ on 'abcb' at 0:
    Input: abcb
    End: 4
    Captures:
    	# 0 : (0,1)
    	# 1 : (1,2)
    	# 2 : (2,3) |}]
  
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
    Regex /(?<G>a)(?<H>b)(?<I>c)\k<I>/ on 'abcc' at 0:
    Input: abcc
    End: 4
    Captures:
    	# 0 : (0,1)
    	# 1 : (1,2)
    	# 2 : (2,3) |}]
  
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
    Regex /(?<G>a(?<H>b(?<I>c)))\k<I>\k<H>\k<G>/ on 'abccbcabc' at 0:
    Input: abccbcabc
    End: 9
    Captures:
    	# 0 : (0,3)
    	# 1 : (1,3)
    	# 2 : (2,3) |}]