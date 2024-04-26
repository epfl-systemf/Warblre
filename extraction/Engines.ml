module type EngineParameters = Extracted.EngineParameters
module Engine = Extracted.Engine

module type Character = sig
  type t

  val equal: t -> t -> bool
  val compare: t -> t -> int
  val numeric_value: t -> int
  val from_numeric_value: int -> t
  val max_numeric_value: int
  val canonicalize: Extracted.RegExpRecord.coq_type -> t -> t
end

module UInt16Character: Character with type t = Unsigned.UInt16.t = struct
  open Unsigned
  type t = UInt16.t
  let equal = UInt16.equal
  let compare = UInt16.compare
  let numeric_value = UInt16.to_int
  let from_numeric_value = UInt16.of_int
  let max_numeric_value = Unsigned.UInt16.to_int Unsigned.UInt16.max_int
  let canonicalize rer ch =
    match rer with
    | { Extracted.RegExpRecord.ignoreCase = false; _ } -> ch
    | _ ->
      let cp = numeric_value ch in
      let u = Encoding.UnicodeUtils.to_upper_case cp in
      let uStr = Encoding.UnicodeUtils.str_to_utf16 u in
      match uStr with
      | cu :: [] ->
        if (numeric_value ch >= 128) && (numeric_value cu < 128) then ch
        else cu
      | _ -> ch
end
module IntCharacter: Character with type t = int = struct
  type t = int
  let equal = Int.equal
  let compare = Int.compare
  let numeric_value i = i
  let from_numeric_value i = i
  let max_numeric_value = 0x10FFFF
  let canonicalize rer i =
    match rer with
    | { Extracted.RegExpRecord.ignoreCase = true; _ } ->
        Encoding.UnicodeUtils.simple_case_fold i
    | _ -> i
end

module CamlString = struct
  type t = Unsigned.UInt16.t list
  let equal = List.equal Unsigned.UInt16.equal
  let length = List.length
  let substring str s e = Utils.List.take (e - s) (Utils.List.drop s str)
  let codeUnitAt str at = List.nth str at

  let to_host = Encoding.Utf16.list_to_string
  let from_host = Encoding.Utf16.list_from_string
end

module CharSet (C: Character) = struct
  module S = Set.Make(C)

  type t = S.t
  let empty = S.empty
  let from_list = S.of_list
  let union = S.union
  let singleton = S.singleton
  let remove_all = S.diff
  let is_empty = S.is_empty
  let contains s c = S.mem c s
  let range l h = S.of_list (List.map C.from_numeric_value (Extracted.List.Range.Nat.Bounds.range (C.numeric_value l) ((C.numeric_value h) + 1)))
  let size = S.cardinal
  let unique err s = if S.cardinal s = 1 then Extracted.Result.Success (S.choose s) else Extracted.Result.Failure err
  let filter s f = S.filter f s
  let exist s p = S.exists p s
end

module CharSets (C: Character) = struct
  include C

  module Common = struct
    let digits: char list = '0' :: '1' :: '2' :: '3' :: '4' :: '5' :: '6' :: '7' :: '8' :: '9' :: []
  
    let ascii_word_characters: char list =
      let str = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789_" in
      List.init (String.length str) (String.get str)
  
    let line_terminators: int list =
      0x000A :: (* <LF> *)
      0x000D :: (* <CR> *)
      0x2028 :: (* <LS> *)
      0x2029 :: (* <PS> *)
      []
  
    let white_spaces: int list =
      9 :: (* <TAB> *)
      11 :: (* <VT> *)
      12 :: (* <FF> *)
      32 :: 
      160 :: 
      5760 ::
      8192 ::
      8193 ::
      8194 ::
      8195 ::
      8196 ::
      8197 ::
      8198 ::
      8199 ::
      8200 ::
      8201 ::
      8202 ::
      8203 :: (* <ZWNBSP> *)
      8239 ::
      8287 ::
      12288 ::
      []
  
    let list_flat_map (type a b) (f: a -> b list) (ls: a list): b list =
      List.flatten (List.map f ls)
  end

  let to_character_list (ls: char list): t list = List.map (fun c -> from_numeric_value (Char.code c)) ls
  
  let all: t list = List.init (max_numeric_value + 1) from_numeric_value
  let line_terminators: t list = (List.map from_numeric_value Common.line_terminators)
  let white_spaces: t list = (List.map from_numeric_value Common.white_spaces)
  let digits: t list = to_character_list Common.digits
  let ascii_word_characters: t list = to_character_list Common.ascii_word_characters
end

module UnicodeProperty = struct
  type t = 
  | Predicate of string

  let equal x y = match x, y with
  | Predicate x, Predicate y -> String.equal x y

  let char_adapter d f = fun c ->
    if (Uchar.is_valid c) then f (Uchar.of_int c)
    else d

  let filter_for up =
    let f = char_adapter false (match up with
    | Predicate "Alphabetic" -> Uucp.Alpha.is_alphabetic
    | Predicate name -> failwith ("Unknown property: " ^ name))
    in
    List.filter f
end

module Utf16Parameters : EngineParameters 
  with type character = Unsigned.UInt16.t
= struct
  module Character = UInt16Character
  type character = Character.t

  module String = struct
    let list_from_string s = s
    let list_to_string s = s
    let advanceStringIndex _ i = i + 1
    let getStringIndex s i = i
    include CamlString
  end
  type string = String.t

  module CharSet = CharSet(Character)
  type char_set = CharSet.t

  module CharSets = CharSets(Character)

  type property = |
  module Property = struct
    let equal _ _ = false
    let code_points _ = failwith "How was the empty type instanciated?"
  end
end

module UnicodeParameters : EngineParameters 
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

module Utf16Engine = Engine(Utf16Parameters)
module UnicodeEngine = Engine(UnicodeParameters)