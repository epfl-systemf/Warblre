open Warblre
open Extracted
open Patterns
open Notations
open Helpers

let str = "aaaaabaac"
let regex = Group (0, Kleene (
    Disjunction (
      Group (1, char 'a'),
      Group (2, char 'b'))))

let () = test_regex regex str