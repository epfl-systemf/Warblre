exception NotImplemented of string

let parse_hex ls =
  int_of_string ("0x" ^ (String.concat "" (List.map (fun c -> String.make 1 c) ls)))

module Utf16 = struct
  type character = Unsigned.uint16
  let char_eq (l: character) (r: character) = Unsigned.UInt16.equal l r
  let char_to_int (c: character): int = Unsigned.UInt16.to_int c
  let char_of_int (i: int): character = Unsigned.UInt16.of_int i
  let cmp (l: character) (r: character): int = Unsigned.UInt16.compare l r


  let to_character_list (ls: char list): character list = List.map (fun c -> char_of_int (Char.code c)) ls
  let all_chars: character list = 
      List.init (Unsigned.UInt16.to_int Unsigned.UInt16.max_int) (fun i -> i)
        |> List.map char_of_int

  let line_terminators: character list = (List.map (char_of_int) ( 
    0x000A :: (* <LF> *)
    0x000D :: (* <CR> *)
    0x2028 :: (* <LS> *)
    0x2029 :: (* <PS> *)
    []))
  let white_spaces: character list = (List.map (char_of_int) ( 
    9 :: (* <TAB> *)
    11 :: (* <VT> *)
    12 :: (* <FF> *)
    32 :: 
    (* 133 ::  *)
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
    []))
  let digits: character list = to_character_list ('0' :: '1' :: '2' :: '3' :: '4' :: '5' :: '6' :: '7' :: '8' :: '9' :: [])
  let ascii_word_characters: character list = to_character_list (
    let str = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789_" in
    List.init (String.length str) (String.get str))

  let codepoint_to_utf16 (code: int) : Unsigned.uint16 list = 
    if code > 0xFFFF then
      (let shifted = (code - 0x10000) in
      let high = (shifted / 0x400) + 0xd800 in
      let low = (shifted mod 0x400) + 0xdc0 in
      (Unsigned.UInt16.of_int high) :: (Unsigned.UInt16.of_int low) :: [])
    else
      (Unsigned.UInt16.of_int code) :: []

  let uchar_to_utf16 (u: Uchar.t) : Unsigned.uint16 list = 
    codepoint_to_utf16 (Uchar.to_int u)

  let string_to_utf16 (str: string): Unsigned.uint16 list = 
    let is = List.init (String.length str) (fun i -> i) in
    let ls = List.map (fun i ->
      let u = StringLabels.get_utf_8_uchar str i in
      if Uchar.utf_decode_is_valid u then
        uchar_to_utf16 (Uchar.utf_decode_uchar u)
      else
        []
    ) is in
    List.flatten ls

  let to_utf8 u: bytes =
    let rec iter u: int list =
      match u with
      | u when u < 0 -> assert false
      | u when u <= 0x007F -> u :: []
      | u when u <= 0x07FF -> (0xC0 lor (u lsr 6)) :: (0x80 lor (u land 0x3F)) :: []
      | u when u <= 0xFFFF -> (0xE0 lor (u lsr 12)) :: (0x80 lor ((u lsr 6) land 0x3F)) :: (0x80 lor (u land 0x3F)):: []
      | u when u <= 0x10FFFF -> (0xF0 lor (u lsr 18)) :: (0x80 lor ((u lsr 12) land 0x3F)) :: (0x80 lor ((u lsr 6) land 0x3F)) :: (0x80 lor (u land 0x3F)):: []
      | _ -> assert false
    in
    let ls = iter u in
    Bytes.init (List.length ls) (fun i -> Char.chr (List.nth ls i))

  let clean_utf16 (str: Unsigned.uint16 list) = 
    let is_high c = (0xd800 <= c) && (c <= 0xdbff) in
    let is_low c = (0xdc00 <= c) && (c <= 0xdfff) in
    let is_normal c = (0x0000 <= c && c < 0xd800) || (0xe000 <= c) in (* (Bool.not (is_high c)) && (Bool.not (is_low c)) in *)
    let rec iter (str: int list) =
      match str with
      | h :: l :: t when is_high h && is_low l -> (
        (Unsigned.UInt16.of_int h) :: (Unsigned.UInt16.of_int l) :: (iter t)
      )
      | h :: t when is_normal h -> (Unsigned.UInt16.of_int h) :: (iter t)
      | _ :: t -> (Unsigned.UInt16.of_int 0xFFFD) :: (iter t)
      | [] -> []
    in
    iter (List.map Unsigned.UInt16.to_int str)

  let utf16_to_string (str: Unsigned.uint16 list) = 
    let is_high c = (0xd800 <= c) && (c <= 0xdbff) in
    let is_low c = (0xdc00 <= c) && (c <= 0xdfff) in
    let is_normal c = (0x0000 <= c && c < 0xd800) || (0xe000 <= c) in (* (Bool.not (is_high c)) && (Bool.not (is_low c)) in *)
    let b = Buffer.create (List.length str) in
    let rec iter (str: int list) =
      match str with
      | h :: l :: t when is_high h && is_low l -> (
        let i = 0x10000 + (h - 0xd800)*0x400 + (l - 0xdc00) in
        assert (is_normal i);
        Buffer.add_utf_8_uchar b (Uchar.of_int i);
        iter t
      )
      | h :: t when is_normal h -> Buffer.add_utf_8_uchar b (Uchar.of_int h); iter t
      | _ :: t -> Buffer.add_utf_8_uchar b (Uchar.of_int 0xFFFD); iter t
      | [] -> ()
    in
    iter (List.map Unsigned.UInt16.to_int str);
    Buffer.contents b 

  type codepoint = int
  let numeric_value (c: codepoint): int = c
  let ascii_letter (c: char): codepoint = Char.code c
  let code_point (c: character): codepoint = char_to_int c

  let to_upper_case (c: codepoint): codepoint list =
      if Uchar.is_valid c then
        match Uucp.Case.Map.to_upper (Uchar.of_int c) with
          | `Self -> c :: []
          | `Uchars ls -> List.map Uchar.to_int ls
      else c :: []
    

  (* The two following functions perform conversions from codepoint to character; should they? *)
  let code_points_to_string (c: codepoint list): character list = List.flatten (List.map codepoint_to_utf16 c)
end

module Unicode = struct
  let string_to_utf8 (str: string): int list = 
    let is = List.init (String.length str) (fun i -> i) in
    List.map (fun i ->
      let u = StringLabels.get_utf_8_uchar str i in
      if Uchar.utf_decode_is_valid u then
        Uchar.to_int (Uchar.utf_decode_uchar u)
      else
        0xFFFD
    ) is

  type character = int
  let char_eq (l: character) (r: character) = Int.equal l r
  let char_to_int (c: character): int = c
  let char_of_int (i: int): character = i
  let cmp (l: character) (r: character): int = Int.compare l r

  let to_character_list (ls: char list): character list = List.map (fun c -> char_of_int (Char.code c)) ls
  let all_chars: character list = 
      List.init (0x10FFFF + 1) (fun i -> i)
        |> List.map char_of_int

  let line_terminators: character list = (List.map (char_of_int) ( 
    0x000A :: (* <LF> *)
    0x000D :: (* <CR> *)
    0x2028 :: (* <LS> *)
    0x2029 :: (* <PS> *)
    []))
  let white_spaces: character list = (List.map (char_of_int) ( 
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
    8239 ::
    8287 ::
    8288 :: (* <ZWNBSP> *)
    12288 ::
    []))
  let digits: character list = to_character_list ('0' :: '1' :: '2' :: '3' :: '4' :: '5' :: '6' :: '7' :: '8' :: '9' :: [])
  let ascii_word_characters: character list = to_character_list (
    let str = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789_" in
    List.init (String.length str) (String.get str))

  let case_fold (c: character): character = 
    if (Uchar.is_valid c) then
      match Uucp.Case.Fold.fold (Uchar.of_int c) with
        | `Self -> c
        | `Uchars (cp :: []) -> Uchar.to_int cp
        | `Uchars _ -> c
    else c

  type unicodeProperty = 
  | Predicate of string

  let up_eq x y = match x, y with
  | Predicate x, Predicate y -> String.equal x y

  let char_adapter d f = fun c ->
    if (Uchar.is_valid c) then f (Uchar.of_int c)
    else d

  let code_points_for up =
    let f = char_adapter false (match up with
    | Predicate "Alphabetic" -> Uucp.Alpha.is_alphabetic
    | Predicate name -> failwith ("Unknown property: " ^ name))
    in
    List.filter f all_chars
end