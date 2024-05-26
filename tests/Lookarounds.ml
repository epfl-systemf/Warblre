open Warblre.OCamlEngines.UnicodeNotations
open Warblre.OCamlEngines.UnicodeTester

let%expect_test "lookahead_0_pos" =
  test_regex
    (cchar 'a' -- (?= (cchar 'b')))
    "ab"
    0 ();
  [%expect {|
    Regex /a(?=b)/ on 'ab' at 0:
    Input: ab
    End: 1
    Captures:
    	None |}]

let%expect_test "lookahead_0_neg_0" =
  test_regex
    (cchar 'a' -- (?= (cchar 'b')))
    "a"
    0 ();
  [%expect {|
    Regex /a(?=b)/ on 'a' at 0:
    No match |}]

let%expect_test "lookahead_0_neg_1" =
  test_regex
    (cchar 'a' -- (?= (cchar 'b')))
    "aa"
    0 ();
  [%expect {|
    Regex /a(?=b)/ on 'aa' at 0:
    No match |}]


let%expect_test "lookbehind_0_pos" =
  test_regex
    ((?<= (cchar 'a')) -- cchar 'b')
    "ab"
    1 ();
  [%expect {|
    Regex /(?<=a)b/ on 'ab' at 1:
    Input: ab
    End: 2
    Captures:
    	None |}]

let%expect_test "lookbehind_0_neg_0" =
  test_regex
    ((?<= (cchar 'a')) -- cchar 'b')
    "b"
    0 ();
  [%expect {|
    Regex /(?<=a)b/ on 'b' at 0:
    No match |}]

let%expect_test "lookbehind_0_neg_1" =
  test_regex
    ((?<= (cchar 'a')) -- cchar 'b')
    "bb"
    1 ();
  [%expect {|
    Regex /(?<=a)b/ on 'bb' at 1:
    No match |}]



let%expect_test "neglookahead_0_pos_0" =
  test_regex
    (cchar 'a' -- (?! (cchar 'b')))
    "aa"
    0 ();
  [%expect {|
    Regex /a(?!b)/ on 'aa' at 0:
    Input: aa
    End: 1
    Captures:
    	None |}]

let%expect_test "neglookahead_0_pos_1" =
  test_regex
    (cchar 'a' -- (?! (cchar 'b')))
    "a"
    0 ();
  [%expect {|
    Regex /a(?!b)/ on 'a' at 0:
    Input: a
    End: 1
    Captures:
    	None |}]

let%expect_test "neglookahead_0_neg" =
  test_regex
    (cchar 'a' -- (?! (cchar 'b')))
    "ab"
    0 ();
  [%expect {|
    Regex /a(?!b)/ on 'ab' at 0:
    No match |}]


let%expect_test "neglookbehind_0_pos_0" =
  test_regex
    ((?<! (cchar 'a')) -- cchar 'b')
    "bb"
    1 ();
  [%expect {|
    Regex /(?<!a)b/ on 'bb' at 1:
    Input: bb
    End: 2
    Captures:
    	None |}]

let%expect_test "neglookbehind_0_pos_1" =
  test_regex
    ((?<! (cchar 'a')) -- cchar 'b')
    "b"
    0 ();
  [%expect {|
    Regex /(?<!a)b/ on 'b' at 0:
    Input: b
    End: 1
    Captures:
    	None |}]

let%expect_test "neglookbehind_0_neg" =
  test_regex
    ((?<! (cchar 'a')) -- cchar 'b')
    "ab"
    1 ();
  [%expect {|
    Regex /(?<!a)b/ on 'ab' at 1:
    No match |}]


(* Note: using [^]  would be better than . *)
let%expect_test "lookbehind_anchor_emulation_pos_0" =
  test_regex
    ((?<! (Dot)) -- !*(cchar 'b'))
    "bbbb"
    0 ();
  [%expect {|
    Regex /(?<!.)b*/ on 'bbbb' at 0:
    Input: bbbb
    End: 4
    Captures:
    	None |}]

  let%expect_test "lookbehind_anchor_emulation_neg_0" =
  test_regex
    ((?<! (Dot)) -- !*(cchar 'b'))
    "bbbb"
    1 ();
  [%expect {|
    Regex /(?<!.)b*/ on 'bbbb' at 1:
    No match |}]

let%expect_test "lookbehind_anchor_emulation_neg_1" =
  test_regex
    ((?<! (Dot)) -- !*(cchar 'b'))
    "abbbb"
    1 ();
  [%expect {|
    Regex /(?<!.)b*/ on 'abbbb' at 1:
    No match |}]

let%expect_test "lookahead_anchor_emulation_pos_0" =
  test_regex
    (!*(cchar 'b') -- (?! (Dot)))
    "bbbb"
    0 ();
  [%expect {|
    Regex /b*(?!.)/ on 'bbbb' at 0:
    Input: bbbb
    End: 4
    Captures:
    	None |}]

let%expect_test "lookbehind_anchor_emulation_neg_0" =
  test_regex
    (!*(cchar 'b') -- (?! (Dot)))
    "bbbba"
    0 ();
  [%expect {|
    Regex /b*(?!.)/ on 'bbbba' at 0:
    No match |}]