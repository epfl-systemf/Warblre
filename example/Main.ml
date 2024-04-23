open Warblre.Notations.UnicodeNotations
open Warblre.Testing.UnicodeTester

let str =
  "aaaaabaπaac"

let regex = 
  group !* (
    Disjunction(
      Disjunction (
        group (char "a"),
        group (char "b")),
      (char ("π"))))

let () = test_regex regex str 0 ()