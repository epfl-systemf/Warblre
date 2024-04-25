module type EngineParameters = Extracted.EngineParameters
module Engine = Extracted.Engine

module Utf16Parameters : EngineParameters 
  with type character = Unsigned.UInt16.t
= struct
  open Unsigned

  type character = UInt16.t
  let unicode = false

  module S = Set.Make(UInt16)
  type char_set = S.t
  type unicode_property = unit

  let unicode_property_eqdec _ _ = true
  let code_points_for _ = []

  module Character = struct
    let eq = UInt16.equal
    let numeric_value = UInt16.to_int
    let from_numeric_value = UInt16.of_int
    let canonicalize rer ch =
      match rer with
      | { Extracted.RegExpRecord.ignoreCase = false; _ } -> ch
      | _ ->
        let cp = numeric_value ch in
        let u = Interop.Utf16.to_upper_case cp in
        let uStr = Interop.Utf16.code_points_to_string u in
        match uStr with
        | cu :: [] ->
          if (numeric_value ch >= 128) && (numeric_value cu < 128) then ch
          else cu
        | _ -> ch

    let list_from_string s = s
    let list_to_string s = s

    let to_host = Encoding.Utf16.list_to_string
    let from_host = Encoding.Utf16.list_from_string
  end

  module CharSet = struct
    
    let empty = S.empty
    let from_list = S.of_list
    let union = S.union
    let singleton = S.singleton
    let remove_all = S.diff
    let is_empty = S.is_empty
    let contains s c = S.mem c s
    let range l h = S.of_list (List.map Character.from_numeric_value (Extracted.List.Range.Nat.Bounds.range (Character.numeric_value l) ((Character.numeric_value h) + 1)))
    let size = S.cardinal
    let unique err s = if S.cardinal s = 1 then Extracted.Result.Success (S.choose s) else Extracted.Result.Failure err
    let filter s f = S.filter f s
    let exist s p = S.exists p s
  end

  module CharSets = struct
    let all = Interop.Utf16.all_chars
    let line_terminators = Interop.Utf16.line_terminators
    let digits = Interop.Utf16.digits
    let white_spaces = Interop.Utf16.white_spaces
    let ascii_word_characters = Interop.Utf16.ascii_word_characters
  end
end

module UnicodeParameters : EngineParameters 
  with type character = int
= struct

  type character = int
  let unicode = true

  module S = Set.Make(Int)
  type char_set = S.t
  type unicode_property = Interop.UnicodeProperties.unicodeProperty

  let unicode_property_eqdec = Interop.UnicodeProperties.up_eq
  let code_points_for up = Interop.UnicodeProperties.filter_for up Interop.Unicode.all_chars

  module Character = struct
    let eq = Int.equal
    let numeric_value i = i
    let from_numeric_value i = i
    let canonicalize rer i =
      match rer with
      | { Extracted.RegExpRecord.ignoreCase = true; _ } ->
            Interop.Unicode.case_fold i
      | _ -> i

    let list_from_string str = Encoding.Unicode.list_from_string (Encoding.Utf16.list_to_string str)
    let list_to_string str = Encoding.Utf16.list_from_string (Encoding.Unicode.list_to_string str)

    let to_host = Encoding.Utf16.list_to_string
    let from_host = Encoding.Utf16.list_from_string
  end

  module CharSet = struct
    let empty = S.empty
    let from_list = S.of_list
    let union = S.union
    let singleton = S.singleton
    let remove_all = S.diff
    let is_empty = S.is_empty
    let contains s c = S.mem c s
    let range l h = S.of_list (List.map Character.from_numeric_value (Extracted.List.Range.Nat.Bounds.range (Character.numeric_value l) ((Character.numeric_value h) + 1)))
    let size = S.cardinal
    let unique err s = if S.cardinal s = 1 then Extracted.Result.Success (S.choose s) else Extracted.Result.Failure err
    let filter s f = S.filter f s
    let exist s p = S.exists p s
  end

  module CharSets = struct
    let all = Interop.Unicode.all_chars
    let line_terminators = Interop.Unicode.line_terminators
    let digits = Interop.Unicode.digits
    let white_spaces = Interop.Unicode.white_spaces
    let ascii_word_characters = Interop.Unicode.ascii_word_characters
  end
end

module Utf16Engine = Engine(Utf16Parameters)
module UnicodeEngine = Engine(UnicodeParameters)