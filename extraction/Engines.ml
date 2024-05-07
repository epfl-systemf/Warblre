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
  
    (* https://262.ecma-international.org/14.0/#prod-LineTerminator *)
    let line_terminators: int list =
      0x000A :: (* <LF> *)
      0x000D :: (* <CR> *)
      0x2028 :: (* <LS> *)
      0x2029 :: (* <PS> *)
      []
  
    let white_spaces: int list =
      0x0009 :: (* <TAB> *)
      0x000B :: (* <VT> *)
      0x000C :: (* <FF> *)
      0xFEFF :: (* <ZWNBSP> *)
      (* USP: Chars whose general category is Zs ('Space_Separator')
         in https://unicode.org/Public/UCD/latest/ucd/UnicodeData.txt *)
      0x20 ::                              
      0xA0 ::
      0x1680 ::
      0x2000 ::
      0x2001 ::
      0x2002 ::
      0x2003 ::
      0x2004 ::
      0x2005 ::
      0x2006 ::
      0x2007 ::
      0x2008 ::
      0x2009 ::
      0x200A ::
      0x202F ::
      0x205F ::
      0x3000 ::
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


