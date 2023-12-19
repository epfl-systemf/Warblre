open Warblre
open Extracted
open Patterns
open Notations
open Helpers

let str = "aaaaabaac"
let regex = Group (None, !* (
    Disjunction (
      Group (None, char 'a'),
      Group (None, char 'b'))))

let () = test_regex regex str 0 ()