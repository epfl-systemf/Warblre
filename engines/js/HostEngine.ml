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

  module Internal = struct
    external search: Js.String.t -> Js.Re.t -> int = "search" [@@mel.send]
    let rmatch: Js.String.t -> Js.Re.t -> (bool * Js.String.t Js.Array.t Js.Nullable.t * Js.Re.result Js.Nullable.t) = [%mel.raw {|
    function (str) { return function (regex) {
      const res = str.match(regex);
      return regex.global ? [true, res, null] : [false, null, res];
    }}
  |}]
    let matchAll: Js.String.t -> Js.Re.t -> Js.String.t Js.Array.t = [%mel.raw {|
      function (str) { return function (regex) {
        return [... str.matchAll(regex)];
      }}
    |}]
  end

  let search (r: regex) (str: Engine.string): int =
    Internal.search (S.to_string str) r

  let test (r: regex) (str: Engine.string): bool =
    Js.Re.test ~str:(S.to_string str) r

  let rmatch (r: regex) (str: Engine.string): (P.string list option, P.string Extracted.ExecArrayExotic.coq_type option) Either.t =
    match Internal.rmatch (S.to_string str) r with
    | (true, res, _) ->
        res
          |> Js.Nullable.toOption
          |> Option.map (fun array -> array
            |> Array.to_list
            |> List.map S.of_string)
          |> Either.left
    | (false, _, res) -> Either.right (Conversion.MatchResult.ocaml_of_js res)

  let matchAll (r: regex) (str: Engine.string): Engine.string Js.Array.t =
    Js.Array.map ~f:(S.of_string) (Internal.matchAll (S.to_string str) r)
end