(** Extract from Rocq to OCaml for Melange.

    We will use these extraction directives twice:
    - Once for "regular" OCaml;
    - Once for OCaml aiming at being compiled by Melange;
    The key difference between these two is that the type BigInt
    is itself instantiated in two different manners, using
    zarith and Js.BigInt respectively.
*)

From Warblre Require Import utils.ExtractionSetup API.
Set Extraction Output Directory ".".
Extraction "Extracted.ml" API.
