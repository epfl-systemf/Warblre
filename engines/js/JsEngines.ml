open Warblre

module JsStringLike: Encoding.StringLike
  with type t = Js.String.t
= struct
  type t = Js.String.t
  let to_string = fun s -> s
  let of_string = fun s -> s
end

module JsCharacter: Engines.Character with type t = Js.String.t = struct
  type t = Js.String.t
  let equal: t -> t -> bool = [%mel.raw {|
    function (l, r) { return l === r; }
  |}]
  let compare: t -> t -> int = [%mel.raw {|
    function (l, r) { return r.charCodeAt(0) - l.charCodeAt(0); }
  |}]
  let numeric_value: t -> int = [%mel.raw {|
    function (c) { return c.charCodeAt(0); }
  |}]
  let from_numeric_value: int -> t = [%mel.raw {|
    function (i) { return String.fromCharCode(i); }
  |}]
  let max_numeric_value = 0xFFFF

  let to_upper_case: t -> t = [%mel.raw {|
    function (ch) {
      const u = ch.toUpperCase();
      if (u.length > 1) {
        return ch;
      }
      else {
        const cu = u.charCodeAt(0);
        if (numeric_value(ch) >= 128 && cu < 128) {
          return ch;
        }
        else {
          return from_numeric_value(cu);
        }
      }
    }
  |}]
  let canonicalize rer ch =
    match rer with
    | { Extracted.RegExpRecord.ignoreCase = false; _ } -> ch
    | _ -> to_upper_case ch
end

module JsString = struct
  type t = Js.String.t
  let equal: t -> t -> bool = [%mel.raw {|
    function (l, r) { return l === r; }
  |}]
  let length (s: t): int = Js.String.length s
  let substring (str: t) (b: int) (e: int): t = Js.String.slice ~start:b ~end_:e str
  let empty_string = {js||js}

  (* Ideally, character = string, but string = 'a list 
      TODO: change mechanization to not use character list, 
      but any type S with typeclass Indexable S character.
  *)
  let list_from_string (s: t) = Array.to_list (Js.String.split ~sep:"" s)
  let list_to_string s = Stdlib.String.concat "" s
end

module JsParameters : Engines.EngineParameters 
  with type character = Js.String.t
  with type string = Js.String.t
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