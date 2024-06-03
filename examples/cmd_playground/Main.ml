module Engine = Warblre_js.Engines.Engine(Warblre_js.JsEngineParameters.JsParameters)
module Printer = Warblre_js.Printers.Printer(Warblre_js.JsEngineParameters.JsParameters)(Warblre_js.JsEngineParameters.JsStringLike)
module Parser = Warblre_js.Parser.Parser(Warblre_js.JsEngineParameters.JsParameters)(Warblre_js.JsEngineParameters.JsStringLike)

let parse (regex: string): ((string, string, Engine.property) Warblre_js.Patterns.coq_Regex, string) Either.t =
  try Either.left (Parser.parseRegex ("/" ^ regex ^ "/"))
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
      let result = Engine.exec (Engine.setLastIndex r (Warblre_js.BigInt.of_int at)) (Warblre_js.JsEngineParameters.JsStringLike.of_string input) in
      Printer.exec_result_to_string result
    in 
    result
  with
    | _ -> "Parsing failed."

let () =

  (* The first two arguments are "node" and the script name *)
  (* https://nodejs.org/docs/latest/api/process.html#process_process_argv *)
  if Array.length Sys.argv != 4 then (Printf.printf "%s\n" "Expected exactly two arguments: <regex> <input string>"; exit 1);

  let pattern = Array.get Sys.argv 2 in
  Printf.printf "Regex: /%s/\n" pattern;
  let input = Array.get Sys.argv 3 in
  Printf.printf "Input: %s\n" input;

  match parse pattern with
  | Either.Left regex ->
    let at = 0 in
    let res = run regex at input in
    Printf.printf "===Result===\n%s\n" res
  | Either.Right msg ->
    Printf.printf "Parsing of regex failed: %s\n" msg