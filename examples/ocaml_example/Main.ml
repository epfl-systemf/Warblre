open Warblre.OCamlEngines.UnicodeNotations
open Warblre.OCamlEngines.UnicodeTester

let str =
  "aaaaabaπaa🧭aaccaa"

let regex = 
  group !* (
    ngroup ("G", char "a") ||
    group (char "b") ||
    (char "π") ||
    (char "🧭"))

let () =
  (* Just match the regex against the string at index 0. *)
  test_exec ~d:true regex ~at:0 str;