open! Warblre
open! Extracted
open! Patterns
open! Notations
open! Helpers

let str =
  "aaaaabaπaac"

let regex = 
  Group (None, !* (
    Disjunction(
      Disjunction (
        Group (None, achar 'a'),
        Group (None, achar 'b')),
      (char ("π")))))

let () = test_regex regex str 0 ()