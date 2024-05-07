open Warblre_ocaml.OCamlEngines.UnicodeNotations
open Warblre_ocaml.OCamlEngines.UnicodeTester

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