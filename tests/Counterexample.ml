open Warblre.Notations.UnicodeNotations
open Warblre.Testing.UnicodeTester

let%expect_test "disjunction_commutativity" =
  let r1 = (cchar 'a') in
  let r2 = ((cchar 'a') -- (cchar 'b')) in
  compare_regexes
    (r1 || r2)
    (r2 || r1)
    "ab"
    0 ();
  [%expect {|
    The two regexes resulted in different matches.
    Regex /a|ab/ on 'ab' at 0:
    Input: ab
    End: 1
    Captures:
    	None
    Regex /ab|a/ on 'ab' at 0:
    Input: ab
    End: 2
    Captures:
    	None |}]

let%expect_test "greedy_question_elimination" =
  let r = (group epsilon) in 
  compare_regexes
    ( !? r )
    ( r || epsilon )
    ""
    0 ();
  [%expect {|
    The two regexes resulted in different matches.
    Regex /()?/ on '' at 0:
    Input:
    End: 0
    Captures:
    	# 0 : Undefined
    Regex /()|/ on '' at 0:
    Input:
    End: 0
    Captures:
    	# 0 : (0,0) |}]

let%expect_test "lazy_question_elimination" =
  let r = ?= (group (cchar 'a')) in
  let f = (!$ 1) -- (cchar 'b') in
  compare_regexes
    ( (!?? r) -- f )
    ( (epsilon || r) -- f )
    "ab"
    0 ();
  [%expect {|
    The two regexes resulted in different matches.
    Regex /(?=(a))??\1b/ on 'ab' at 0:
    No match
    Regex /(?:|(?=(a)))\1b/ on 'ab' at 0:
    Input: ab
    End: 2
    Captures:
    	# 0 : (0,1) |}]