open Warblre.Engines
open Warblre.Printers

(* Parameters for the engine we will use. *)
module Parameters = Warblre.OCamlEngineParameters.UnicodeParameters
module StringLike = Warblre.OCamlEngineParameters.Utf16StringLike

(* Instantiate the engine, and setup some utilities. *)
module Engine = Engine(Parameters)
module Printer = Printer(Parameters)(StringLike)
open Warblre.Notations.CharNotations(Parameters)(StringLike)

(* Let's create a regex using the notations we just imported. *)

(* Disregard the spaces *)
(* ( (?: (?<G>a) | (b) | π | (🧭) )* ) *)
let regex =
	group !* (
    ngroup ("G", char "a") ||
    group (char "b") ||
    (char "π") ||
    (char "🧭"))

(* Flags are used to configure the engine; we will just enable reporting of capture indices (d). *)
let flags = Warblre.Extracted.RegExpFlags.({
	d = true;
	g = false;
	i = false;
	m = false;
	s = false;
	u = ();
	y = false;
})

let input =
	"aaaaabaπaa🧭aaccaa"

let () =
	Printf.printf "Regex: %s\n" (Printer.regex_to_string regex);
	Printf.printf "Input: '%s'\n" input;
	let instance = Engine.initialize regex flags in
        match Engine.exec instance (StringLike.of_string input) with
	| Null _ -> Printf.printf "No match.\n"
	| Exotic (result, _) -> Printf.printf "%s\n" (Printer.array_exotic_to_string result)
