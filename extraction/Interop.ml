exception NotImplemented of string

type character = Unsigned.uint16
let char_eq (l: character) (r: character) = Unsigned.UInt16.equal l r
let char_to_int (c: character): int = Unsigned.UInt16.to_int c
let char_of_int (i: int): character = Unsigned.UInt16.of_int i

let parse_hex d1 d2 = int_of_string ("0x" ^ (String.make 1 d1) ^ (String.make 1 d2))

let to_character_list (ls: char list): character list = List.map (fun c -> char_of_int (Char.code c)) ls
let all_chars: character list = (List.init (Unsigned.UInt16.to_int Unsigned.UInt16.max_int) (char_of_int))
let line_terminators: character list = to_character_list ('\n' :: '\r' :: [])
let white_spaces: character list = (List.map (char_of_int) ( 
  9 :: (* <TAB> *)
  11 :: (* <VT> *)
  12 :: (* <FF> *)
  32 :: 
  133 :: 
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


let uchar_to_utf16 (u: Uchar.t) : Unsigned.uint16 list = 
  let code:int = Uchar.to_int u in
  if code > 0xFFFF then
    (let shifted = (code - 0x10000) in
    let high = (shifted / 0x400) + 0xd800 in
    let low = (shifted mod 0x400) + 0xdc0 in
    (Unsigned.UInt16.of_int high) :: (Unsigned.UInt16.of_int low) :: [])
  else
    (Unsigned.UInt16.of_int code) :: []

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

let utf16_to_string (str: Unsigned.uint16 list) = 
  let b = Buffer.create (List.length str) in
  let rec iter (str: Unsigned.uint16 list) =
    match str with
    | [] -> ()
    | h :: t1 ->
      let hi = Unsigned.UInt16.to_int h in 
      (* Note that the upper bound can be discussed, depending on whether a lone low surrogate should be an error or not *)
      if hi >= 0xd800 && hi <= 0xdbff then (
        (* Surrogate pair! *)
        match t1 with
        | [] ->
          (* Printf.printf "Unpaired surrogate: %d\n" hi; *)
          Buffer.add_utf_8_uchar b (Uchar.of_int hi)
        | l :: t2 ->
          let li = Unsigned.UInt16.to_int l in
          assert ((0xd800 <= hi) && (hi <= 0xdbff));
          assert ((0xdc00 <= li) && (li <= 0xdfff));
          let i = 0x10000 + (hi - 0xd800)*0x400 + (li - 0xdc00) in
          Buffer.add_utf_8_uchar b (Uchar.of_int i);
          iter t2
      )
      else (
        Buffer.add_utf_8_uchar b (Uchar.of_int hi);
        iter t1
      )
  in
  iter str;
  Buffer.contents b

type codepoint = Uchar.t
let numeric_value (c: codepoint): int = Uchar.to_int c
let ascii_letter (c: char): codepoint = Uchar.of_char c
let code_point (c: character): codepoint = Uchar.of_int (char_to_int c)

let to_upper_case (c: codepoint): codepoint list =
  match Uucp.Case.Map.to_upper c with
  | `Self -> c :: []
  | `Uchars ls -> ls

(* The two following functions perform conversions from codepoint to character; should they? *)
let code_points_to_string (c: codepoint list): character list = List.flatten (List.map uchar_to_utf16 c)

let case_fold (c: character): character = raise (NotImplemented "case_fold")
