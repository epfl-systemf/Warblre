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
    Matched 1 characters ([0-1]) in 'ab' (length=2)
    Matched 2 characters ([0-2]) in 'ab' (length=2) |}]

let%expect_test "greedy_question_elimination" =
  let r = (group epsilon) in 
  compare_regexes
    ( !? r )
    ( r || epsilon )
    ""
    0 ();
  [%expect {|
    The two regexes resulted in different matches.
    Matched 0 characters ([0-0]) in '' (length=0)
    Group 1: undefined
    Matched 0 characters ([0-0]) in '' (length=0)
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
    No match on 'ab'
    Matched 2 characters ([0-2]) in 'ab' (length=2)
    Group 1: 'a' ([0-1]) |}]