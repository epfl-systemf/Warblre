open! Warblre.Extracted.Regex.Patterns
open Warblre.Helpers
open Warblre.Notations

let%expect_test "sequence" =
  test_regex
    ((char 'a') -- (char 'b') -- (char 'b'))
    "abbb";
  [%expect {| Matched 3 characters in 'abbb' (length=4) |}]


let%expect_test "capture_reset" =
  test_regex
    !*(   group (1, char 'a')
    ||  group (2, char 'b'))
    "ab";
  [%expect {|
    Matched 2 characters in 'ab' (length=2)
    Group 1: undefined
    Group 2: 'b' (1-2) |}]

let%expect_test "tmp" = 
  test_regex
    (group (0, !*(
          group (1, char 'a')
      ||  group (2, char 'b'))))
    "aaaaabaac";
  [%expect {|
    Matched 8 characters in 'aaaaabaac' (length=9)
    Group 0: 'aaaaabaa' (0-8)
    Group 1: 'a' (7-8)
    Group 2: undefined |}]