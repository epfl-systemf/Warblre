module Utf16 : Encoding.Character with type character = Unsigned.UInt16.t = struct
  type character = Unsigned.UInt16.t
  let cmp (l: character) (r: character): int = Unsigned.UInt16.compare l r

  let chars_from_int s = List.map Unsigned.UInt16.of_int (Encoding.UnicodeUtils.to_utf16 s)

  let char_from_int c = Utils.List.unique (chars_from_int c)

  let char_to_int (c: character) = Unsigned.UInt16.to_int c

  let list_from_string (str: string): character list = 
    let is = List.init (String.length str) (fun i -> i) in
    Utils.List.flat_map (fun i ->
      let u = StringLabels.get_utf_8_uchar str i in
      if Uchar.utf_decode_is_valid u then
        chars_from_int (Uchar.to_int (Uchar.utf_decode_uchar u))
      else
        []
    ) is

  let list_to_string (str: character list): string = 
    let b = Buffer.create (List.length str) in
    let rec iter (str: int list) =
      match str with
      | h :: l :: t when Encoding.UnicodeUtils.is_high_surrogate h && Encoding.UnicodeUtils.is_low_surrogate l -> (
        let i = 0x10000 + (h - 0xd800)*0x400 + (l - 0xdc00) in
        assert (Encoding.UnicodeUtils.is_normal i);
        Buffer.add_utf_8_uchar b (Uchar.of_int i);
        iter t
      )
      | h :: t when Encoding.UnicodeUtils.is_normal h -> Buffer.add_utf_8_uchar b (Uchar.of_int h); iter t
      | _ :: t -> Buffer.add_utf_8_uchar b (Uchar.of_int 0xFFFD); iter t
      | [] -> ()
    in
    iter (List.map Unsigned.UInt16.to_int str);
    Buffer.contents b 
end

module Unicode : Encoding.Character with type character = int = struct
  type character = int
  let cmp (l: character) (r: character): int = Int.compare l r

  let chars_from_int (code: int) : character list = code :: []

  let char_from_int c = Utils.List.unique (chars_from_int c)

  let char_to_int (c: character) = c

  let list_from_string (str: string): character list = 
    let is = List.init (String.length str) (fun i -> i) in
    Utils.List.flat_map (fun i ->
      let u = StringLabels.get_utf_8_uchar str i in
      if Uchar.utf_decode_is_valid u then
        (Uchar.to_int (Uchar.utf_decode_uchar u)) :: []
      else
        []
    ) is

    let list_to_string (str: character list): string = 
      let b = Buffer.create (List.length str) in
      List.iter ( fun c ->
        if Uchar.is_valid c then
          Buffer.add_utf_8_uchar b (Uchar.of_int c)
        else
          Buffer.add_utf_8_uchar b Encoding.UnicodeUtils.replacement_char
      ) str;
      Buffer.contents b 
end

module Utf16StringLike : Encoding.StringLike
  with type t = Utf16.character list
= struct
  type t = Utf16.character list
  let to_string = Utf16.list_to_string
  let of_string = Utf16.list_from_string
end

module UInt16Character: Engines.Character with type t = Unsigned.UInt16.t = struct
  open Unsigned
  type t = UInt16.t
  let equal = UInt16.equal
  let compare = UInt16.compare
  let numeric_value = UInt16.to_int
  let from_numeric_value = UInt16.of_int
  let max_numeric_value = Unsigned.UInt16.to_int Unsigned.UInt16.max_int
  let canonicalize rer ch =
    let to_upper_case (c: int): int list =
      if Uchar.is_valid c then
        match Uucp.Case.Map.to_upper (Uchar.of_int c) with
          | `Self -> c :: []
          | `Uchars ls -> List.map Uchar.to_int ls
      else c :: []
    in
    match rer with
    | { Extracted.RegExpRecord.ignoreCase = false; _ } -> ch
    | _ ->
      let cp = numeric_value ch in
      let u = to_upper_case cp in
      let uStr = Encoding.UnicodeUtils.str_to_utf16 u in
      match uStr with
      | cu :: [] ->
        let cu = Utf16.char_from_int cu in
        if (numeric_value ch >= 128) && (numeric_value cu < 128) then ch
        else cu
      | _ -> ch
end
module IntCharacter: Engines.Character with type t = int = struct
  type t = int
  let equal = Int.equal
  let compare = Int.compare
  let numeric_value i = i
  let from_numeric_value i = i
  let max_numeric_value = 0x10FFFF



  module M = Map.Make(Int)
  (* S-rules from https://unicode.org/Public/UCD/latest/ucd/CaseFolding.txt *)
  let simple_folds = M.of_seq (List.to_seq (
    (0x1E9E, 0x00DF) ::
    (0x1F88, 0x1F80) ::
    (0x1F89, 0x1F81) ::
    (0x1F8A, 0x1F82) ::
    (0x1F8B, 0x1F83) ::
    (0x1F8C, 0x1F84) ::
    (0x1F8D, 0x1F85) ::
    (0x1F8E, 0x1F86) ::
    (0x1F8F, 0x1F87) ::
    (0x1F98, 0x1F90) ::
    (0x1F99, 0x1F91) ::
    (0x1F9A, 0x1F92) ::
    (0x1F9B, 0x1F93) ::
    (0x1F9C, 0x1F94) ::
    (0x1F9D, 0x1F95) ::
    (0x1F9E, 0x1F96) ::
    (0x1F9F, 0x1F97) ::
    (0x1FA8, 0x1FA0) ::
    (0x1FA9, 0x1FA1) ::
    (0x1FAA, 0x1FA2) ::
    (0x1FAB, 0x1FA3) ::
    (0x1FAC, 0x1FA4) ::
    (0x1FAD, 0x1FA5) ::
    (0x1FAE, 0x1FA6) ::
    (0x1FAF, 0x1FA7) ::
    (0x1FBC, 0x1FB3) ::
    (0x1FCC, 0x1FC3) ::
    (0x1FD3, 0x0390) ::
    (0x1FE3, 0x03B0) ::
    (0x1FFC, 0x1FF3) ::
    (0xFB05, 0xFB06) ::
    []
  ))
  let canonicalize rer i =
    (* UUCP does not provide simple case folding, so we implement it ourselves *)
    let simple_case_fold (c: int): int = 
      (* Is there a S-rule for this char? *)
      if M.mem c simple_folds then 
        (* Use it *)
        M.find c simple_folds
      (* o/w, is the chracter valid? *)
      else if (Uchar.is_valid c) then
        (* Do full case folding *)
        match Uucp.Case.Fold.fold (Uchar.of_int c) with
          (* No mapping -> return self *)
          | `Self -> c
          (* All length 1 mappings are C-rules, so we should use the mapping *)
          | `Uchars (cp :: []) -> Uchar.to_int cp
          (* Simple case folding cannot generate a string of length > 1, so this is an F-rule; we should not use it *)
          | `Uchars _ -> c
      (* Stray surrogates (i.e. what's left) are not folded *)
      else
        c 
    in

    match rer with
    | { Extracted.RegExpRecord.ignoreCase = true; _ } ->
        simple_case_fold i
    | _ -> i
end

module CamlString = struct
  type t = Unsigned.UInt16.t list
  let equal = List.equal Unsigned.UInt16.equal
  let length = List.length
  let substring str s e = Utils.List.take (e - s) (Utils.List.drop s str)
  let codeUnitAt str at = List.nth str at
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

module Utf16Parameters : Engines.EngineParameters 
  with type character = Unsigned.UInt16.t
  with type string = Utf16.character list
= struct
  module Character = UInt16Character
  type character = Character.t

  module String = struct
    let list_from_string s = s
    let list_to_string s = s
    let advanceStringIndex _ i = i + 1
    let getStringIndex _ i = i
    include CamlString
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

module UnicodeParameters : Engines.EngineParameters 
  with type character = int
  with type string = Unsigned.UInt16.t list
= struct
  module Character = IntCharacter
  type character = Character.t

  module String = struct
    let list_from_string str = Unicode.list_from_string (Utf16.list_to_string str)
    let list_to_string str = Utf16.list_from_string (Unicode.list_to_string str)

    module Ops = Extracted.API.Utils.UnicodeOps(struct
      type coq_Utf16CodeUnit = Unsigned.UInt16.t
      type coq_Utf16String = Unsigned.UInt16.t list
      let length = List.length
      let codeUnitAt = List.nth
      let is_leading_surrogate c = Encoding.UnicodeUtils.is_high_surrogate (Unsigned.UInt16.to_int c)
      let is_trailing_surrogate c = Encoding.UnicodeUtils.is_low_surrogate (Unsigned.UInt16.to_int c)
    end)
    let advanceStringIndex s i = Ops.advanceStringIndex s i
    let getStringIndex s i = Ops.getStringIndex s i


    include CamlString
  end
  type string = String.t

  module CharSet = Engines.CharSet(Character)
  type char_set = CharSet.t

  module CharSets = Engines.CharSets(Character)

  type property = UnicodeProperty.t
  module Property = struct
    let equal = UnicodeProperty.equal
    let code_points up = UnicodeProperty.filter_for up CharSets.all
  end
end

module Utf16Engine = Engines.Engine(Utf16Parameters)
module UnicodeEngine = Engines.Engine(UnicodeParameters)

module Utf16Notations = Notations.CharNotations(Utf16Parameters)(Utf16StringLike)
module UnicodeNotations = struct
  open Patterns
  module Base = Notations.CharNotations(UnicodeParameters)(Utf16StringLike)
  include Base

  let uprop n = AtomEsc (ACharacterClassEsc (UnicodeProp (Obj.magic (UnicodeProperty.Predicate n))))
end

module Utf16Printer = Printers.Printer(Utf16Parameters)(Utf16StringLike)
module UnicodePrinter = Printers.Printer(UnicodeParameters)(Utf16StringLike)

module Utf16Tester = Testing.Tester(Utf16Parameters)(Utf16StringLike)
module UnicodeTester = Testing.Tester(UnicodeParameters)(Utf16StringLike)