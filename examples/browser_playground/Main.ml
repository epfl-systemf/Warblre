module Engine = Warblre_js.Engines.Engine(Warblre_js.JsEngineParameters.JsParameters)
module Printer = Warblre_js.Printers.Printer(Warblre_js.JsEngineParameters.JsParameters)(Warblre_js.JsEngineParameters.JsStringLike)
module Parser = Warblre_js.Parser.Parser(Warblre_js.JsEngineParameters.JsParameters)(Warblre_js.JsEngineParameters.JsStringLike)

(*
    A tiny application which retrieves a regex an input string from
    HTML forms, parses and compiles the former and then runs it against the latter.
    
    The result is then printed back on the web page.
*)

external window: Dom.element = "window"
external document : Dom.document = "document"
external document_get_by_id: Dom.document -> string -> Dom.element = "getElementById" [@@mel.send]

let get_by_id id = document_get_by_id document id
external set_value : Dom.element -> string -> unit = "value" [@@mel.set]
external get_value : Dom.element -> string = "value" [@@mel.get]
external set_inner_html : Dom.element -> string -> unit = "innerHTML" [@@mel.set]
external add_event_listener : Dom.element -> string -> (unit -> unit) -> unit = "addEventListener" [@@mel.send]

let parse (regex: string): ((string, string, Engine.property) Warblre_js.Patterns.coq_Regex, string) Either.t =
  try Either.left (Parser.parseRegex regex)
  with e -> match Option.bind (Js.Exn.asJsExn e) Js.Exn.message with
            | None -> Either.right "Unspecified parsing error."
            | Some msg -> Either.right msg

let run (regex: (string, string, Engine.property) Warblre_js.Patterns.coq_Regex) (at: int) (input: string): string =
  try 
    let flags = Warblre_js.Extracted.({
      RegExpFlags.d = false;
      RegExpFlags.g = false;
      RegExpFlags.i = false;
      RegExpFlags.m = false;
      RegExpFlags.s = false;
      RegExpFlags.u = ();
      RegExpFlags.y = false;
    }) in
    let r =  Engine.initialize regex flags in
    let result = 
      match Engine.exec (Engine.setLastIndex r (Warblre_js.BigInt.of_int at)) (Warblre_js.JsEngineParameters.JsStringLike.of_string input) with
      | Null _ -> "No match found."
      | Exotic ({ array = array ; _}, _) -> Option.get (List.nth array 0)
    in 
    result
  with
    | _ -> "Parsing failed."

let input_regex () = get_by_id "regex"
let input_string () = get_by_id "string"
let output_regex () = get_by_id "pretty-regex"
let output_string () = get_by_id "output"

(* Retrieves the data from the form, delegates matching to run and display the result. *)
let recompute () = 
  set_value (output_string ()) "...";
  let pattern = get_value (input_regex ()) in
  match parse pattern with
  | Either.Left regex ->
    let at = 0 in
    let input = get_value (input_string ()) in
    let res = run regex at input in
    set_value (output_regex ()) (Printer.regex_to_string regex);
    set_value (output_string ()) res
  | Either.Right msg ->
    set_value (output_regex ()) msg;
    set_value (output_string ()) msg

let () = 
  add_event_listener window "load" (fun _ ->
    add_event_listener (input_regex ()) "change" recompute;
    add_event_listener (input_string ()) "change" recompute;

    let pattern = "/.[a-cz]*/" in
    let input = "yaabczzzkk" in
    set_value (input_regex ()) pattern;
    set_value (input_string ()) input;
    recompute())