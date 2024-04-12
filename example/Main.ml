open Warblre.Notations.UnicodeNotations
open Warblre.Testing.UnicodeTester

let str =
  "aaaaabaπaac"

let regex = 
  group !* (
    Disjunction(
      Disjunction (
        Group (None, cchar 'a'),
        Group (None, cchar 'b')),
      (char ("π"))))

let () = test_regex regex str 0 ()