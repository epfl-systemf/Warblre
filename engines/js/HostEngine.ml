(*
  An API to manipulate the host regex engine (i.e. the one provided by Node.js, Chromium, Firefox, ...).
  The api is meant to resemble the one of the extracted engine.
*)
module HostEngine (P: Engines.EngineParameters) (S: Encoding.StringLike with type t := P.string) = struct
  module Engine = Engines.Engine(P)  
  module Printer = Printers.Printer(P)(S)
  module Conversion = ArrayExotic.ArrayExotic(P)(S)
  type regex = Js.Re.t 

  let initialize (regex: (Engine.character, Engine.string, P.property) Extracted.Patterns.coq_Regex) (flags: Extracted.RegExpFlags.coq_type): regex =
    let regex_string = Printer.regex_to_string ~delimited:false ~strict:true regex in
    let flags_string = Printer.flags_to_string flags in
    Js.Re.fromStringWithFlags regex_string ~flags:flags_string

  let setLastIndex (r: regex) (at: int): unit = Js.Re.setLastIndex r at

  let exec (r: regex) (str: Engine.string): (P.string) Extracted.ExecArrayExotic.coq_type option =
    let js_result = Js.Re.exec ~str:(S.to_string str) r in
    Conversion.MatchResult.ocaml_of_js (Js.Nullable.fromOption js_result)
end