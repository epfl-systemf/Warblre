module Common = struct
  let parse_hex ls =
    int_of_string ("0x" ^ (String.concat "" (List.map (fun c -> String.make 1 c) ls)))

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

module UnicodeProperties = struct
  type unicodeProperty = 
  | Predicate of string

  let up_eq x y = match x, y with
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

module type InteropSig = sig
  include Encoding.Character
  val max: int
  type property
end

module Interop (I: InteropSig) = struct
  include I

  let to_character_list (ls: char list): character list = List.map (fun c -> char_from_int (Char.code c)) ls
  let all_chars: character list = 
      List.init (max + 1) char_from_int

  let line_terminators: character list = (List.map char_from_int Common.line_terminators)
  let white_spaces: character list = (List.map char_from_int Common.white_spaces)
  let digits: character list = to_character_list Common.digits
  let ascii_word_characters: character list = to_character_list Common.ascii_word_characters
end

module Utf16Sig : InteropSig
  with type character = Unsigned.uint16
  with type property = unit
= struct
  include Encoding.Utf16
  let max: int = Unsigned.UInt16.to_int Unsigned.UInt16.max_int
  type property = unit
end

module UnicodeSig : InteropSig
  with type character = int
  with type property = UnicodeProperties.unicodeProperty
= struct
  include Encoding.Unicode
  let max: int = 0x10FFFF
  type property = UnicodeProperties.unicodeProperty
end

module Utf16 = struct
  module Base = Interop(Utf16Sig)
  include Base

  let code_points_to_string (c: Encoding.codepoint list): character list = List.flatten (List.map chars_from_int c)

  let to_upper_case (c: Encoding.codepoint): Encoding.codepoint list =
    if Uchar.is_valid c then
      match Uucp.Case.Map.to_upper (Uchar.of_int c) with
        | `Self -> c :: []
        | `Uchars ls -> List.map Uchar.to_int ls
    else c :: []
end

module Unicode = struct
  module Base = Interop(UnicodeSig)
  include Base

  let case_fold (c: character): character = 
    if (Uchar.is_valid c) then
      match Uucp.Case.Fold.fold (Uchar.of_int c) with
        | `Self -> c
        | `Uchars (cp :: []) -> Uchar.to_int cp
        | `Uchars _ -> c
    else c

  let code_points_for_property up = UnicodeProperties.filter_for up all_chars
end