open Warblre.Notations.UnicodeNotations
open Warblre.Testing.UnicodeTester

let str =
  "aaaaabaπaa🧭aaccaa"

let regex = 
  group !* (
    ngroup ("G", char "a") ||
    group (char "b") ||
    (char "π") ||
    (char "🧭"))

let () =
  test_exec ~d:true regex ~at:0 str;