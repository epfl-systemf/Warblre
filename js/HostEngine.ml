open Js_of_ocaml
open Warblre

module HostEngine (P: Engines.EngineParameters) (S: Encoding.StringLike with type t := P.string) = struct
  open Engines.Engine(P)
  module Printer = Printers.Printer(P)(S)
  module Conversion = Conversion.Conversion(P)(S)
  type regex = Js.regExp Js.t

  let initialize (regex: (character, string) Extracted.Patterns.coq_Regex) (flags: Extracted.RegExpFlags.coq_type): regex =
    let regex_string = Printer.regex_to_string ~delimited:false ~strict:true regex in
    let flags_string = Printer.flags_to_string flags in
    new%js Js.regExp_withFlags (Js.bytestring regex_string) (Js.string flags_string)

  let setLastIndex (r: regex) (at: int): unit = r##.lastIndex := at

  let exec (r: regex) (str: string): (character, string) Extracted.ExecArrayExotic.coq_type option =
    let js_result = r##exec (Js.bytestring (S.to_string str)) in
    Conversion.MatchResult.ocaml_of_js js_result
end