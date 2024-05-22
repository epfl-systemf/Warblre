open Warblre.Printers
module JsEngine = Warblre_js.JsEngines.JsEngine
module P = Printer(Warblre_js.JsEngines.JsParameters)(Warblre_js.JsEngines.JsStringLike)
open! P

external window: Dom.element = "window"
external document : Dom.document = "document"
external document_get_by_id: Dom.document -> string -> Dom.element = "getElementById" [@@mel.send]

let get_by_id id = document_get_by_id document id
external set_value : Dom.element -> string -> unit = "value" [@@mel.set]
external get_value : Dom.element -> string = "value" [@@mel.get]
external set_inner_html : Dom.element -> string -> unit = "innerHTML" [@@mel.set]
external add_event_listener : Dom.element -> string -> (unit -> unit) -> unit = "addEventListener" [@@mel.send]

let run (pattern: string) (at: int) (input: string): string =
  try 
    let regex = Warblre_js.JsEngines.JsEngine.Regexpp.parseRegex pattern in
    let flags = Warblre.Extracted.({
      RegExpFlags.d = false;
      RegExpFlags.g = false;
      RegExpFlags.i = false;
      RegExpFlags.m = false;
      RegExpFlags.s = false;
      RegExpFlags.u = ();
      RegExpFlags.y = false;
    }) in
    let r =  JsEngine.initialize regex flags in
    let result = 
      match JsEngine.exec (JsEngine.setLastIndex r at) (Warblre_js.JsEngines.JsStringLike.of_string input) with
      | Null _ -> "No match found."
      | Exotic ({ array = array ; _}, _) -> Option.get (List.nth array 0)
    in 
    result
  with
    | _ -> "Parsing failed."

let input_regex () = get_by_id "regex"
let input_string () = get_by_id "string"
let output_string () = get_by_id "output"
let recompute () = 
  set_value (output_string ()) "...";
  let pattern = get_value (input_regex ()) in
  let at = 0 in
  let input = get_value (input_string ()) in
  let res = run pattern at input in
  set_value (output_string ()) res

let () = 
  add_event_listener window "load" (fun _ ->
    add_event_listener (input_regex ()) "change" recompute;
    add_event_listener (input_string ()) "change" recompute;

    let pattern = "/.[a-cz]*/" in
    let input = "yaabczzzkk" in
    set_value (input_regex ()) pattern;
    set_value (input_string ()) input;
    recompute())