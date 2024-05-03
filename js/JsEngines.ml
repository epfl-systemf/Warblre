open Warblre
open Js_of_ocaml

module JsStringLike: Encoding.StringLike
  with type t = Js.js_string Js.t
= struct
  type t = Js.js_string Js.t
  let to_string = Js.to_string
  let of_string = Js.string
end

module JsCharacter: Engines.Character with type t = Js.js_string Js.t = struct
  type t = Js.js_string Js.t
  external equal: t -> t -> bool = "char_utf16_equal"
  external compare: t -> t -> int = "char_utf16_compare"
  external numeric_value: t -> int = "char_utf16_numeric_value"
  external from_numeric_value: int -> t = "char_utf16_from_numeric_value"
  let max_numeric_value = 0xFFFF

  external to_upper_case: t -> t = "char_utf16_to_uppercase"
  let canonicalize rer ch =
    match rer with
    | { Extracted.RegExpRecord.ignoreCase = false; _ } -> ch
    | _ -> to_upper_case ch
end

module JsString = struct
  type t = Js.js_string Js.t
  external equal: t -> t -> bool = "string_equal"
  let length (s: t): int = s##.length
  let substring (str: t) (b: int) (e: int): t = str##slice b e

  let empty_string = (Js.string "")

  (* Ideally, character = string, but string = 'a list 
      TODO: change mechanization to not use character list, 
      but any type S with typeclass Indexable S character.
  *)
  let list_from_string (s: t) =
    (s##split empty_string)
      |> Js.str_array
      |> Js.to_array
      |> Array.to_list
  let list_to_string s =
    s |> Array.of_list
      |> Js.array
      |> (fun a -> a##join empty_string)
end

module JsParameters : Engines.EngineParameters 
  with type character = Js.js_string Js.t
  with type string = Js.js_string Js.t
= struct
  module Character = JsCharacter
  type character = Character.t

  module String = struct
    include JsString
    let advanceStringIndex _ i = i + 1
    let getStringIndex _ i = i
  end
  type string = String.t

  module CharSet = Engines.CharSet(Character)
  type char_set = CharSet.t

  module CharSets = Engines.CharSets(Character)

  type property = |
  module Property = struct
    let equal _ _ = false
    let code_points _ = failwith "How was the empty type instanciated?"
  end
end

(* module UnicodeParameters : EngineParameters 
  with type character = int
  with type string = Unsigned.UInt16.t list
= struct
  module Character = IntCharacter
  type character = Character.t

  module String = struct
    let list_from_string str = Encoding.Unicode.list_from_string (Encoding.Utf16.list_to_string str)
    let list_to_string str = Encoding.Utf16.list_from_string (Encoding.Unicode.list_to_string str)

    module Ops = Extracted.UnicodeOps(struct
      type coq_Utf16CodeUnit = Unsigned.UInt16.t
      type coq_Utf16String = Unsigned.UInt16.t list
      let length = List.length
      let codeUnitAt = List.nth
      let is_leading_surrogate c = Encoding.UnicodeUtils.is_high_surrogate (Unsigned.UInt16.to_int c)
      let is_trailing_surrogate c = Encoding.UnicodeUtils.is_low_surrogate (Unsigned.UInt16.to_int c)
    end)
    let advanceStringIndex s i = Utils.Result.get (Ops.advanceStringIndex s i)
    let getStringIndex s i = Utils.Result.get (Ops.getStringIndex s i)


    include CamlString
  end
  type string = String.t

  module CharSet = CharSet(Character)
  type char_set = CharSet.t

  module CharSets = CharSets(Character)

  type property = UnicodeProperty.t
  module Property = struct
    let equal = UnicodeProperty.equal
    let code_points up = UnicodeProperty.filter_for up CharSets.all
  end
end
*)
module JsEngine = Engines.Engine(JsParameters)
(* module UnicodeEngine = Engine(UnicodeParameters) *)