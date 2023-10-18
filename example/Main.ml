open Warblre
open Extracted
open Regex
open Patterns
open Helpers

let str = "aaaaabaac"
let regex = Group (0, Kleene (
    Disjunction (
      Group (1, Char ((fun c -> c == 'a'), false)),
      Group (2, Char ((fun c -> c == 'b'), false)))))

let () = test_regex regex str