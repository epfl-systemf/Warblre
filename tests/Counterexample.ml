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
    /a|ab/ matched 1 characters ([0-1]) in 'ab' (length=2)
    /ab|a/ matched 2 characters ([0-2]) in 'ab' (length=2) |}]

let%expect_test "greedy_question_elimination" =
  let r = (group epsilon) in 
  compare_regexes
    ( !? r )
    ( r || epsilon )
    ""
    0 ();
  [%expect {|
    The two regexes resulted in different matches.
    /()?/ matched 0 characters ([0-0]) in '' (length=0)
    Group 1: undefined
    /()|/ matched 0 characters ([0-0]) in '' (length=0)
    Group 1: '' ([0-0]) |}]

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
    /(?=(a))??\1b/ matched nothing on 'ab'
    /(?:|(?=(a)))\1b/ matched 2 characters ([0-2]) in 'ab' (length=2)
    Group 1: 'a' ([0-1]) |}]