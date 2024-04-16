type codepoint = int

module Utf8Utils = struct
  let from_int (u: int) : char list =
    match u with
    | u when u < 0 -> assert false
    | u when u <= 0x007F -> Char.chr u :: []
    | u when u <= 0x07FF -> Char.chr (0xC0 lor (u lsr 6)) :: Char.chr (0x80 lor (u land 0x3F)) :: []
    | u when u <= 0xFFFF -> Char.chr (0xE0 lor (u lsr 12)) :: Char.chr (0x80 lor ((u lsr 6) land 0x3F)) :: Char.chr (0x80 lor (u land 0x3F)) :: []
    | u when u <= 0x10FFFF -> Char.chr (0xF0 lor (u lsr 18)) :: Char.chr (0x80 lor ((u lsr 12) land 0x3F)) :: Char.chr (0x80 lor ((u lsr 6) land 0x3F)) :: Char.chr (0x80 lor (u land 0x3F)) :: []
    | _ -> failwith "Int is to big for a unicode character!"

    
    let is_high_surrogate (c: int) = (0xd800 <= c) && (c <= 0xdbff)
    let is_low_surrogate (c: int) = (0xdc00 <= c) && (c <= 0xdfff)
    (* I.e. not a surrogate *)
    let is_normal (c: int) = (0x0000 <= c && c < 0xd800) || (0xe000 <= c)

    let replacement_int = 0xFFFD
    let replacement_uchar = Uchar.of_int replacement_int
end

module type Character = sig
  type character

  val cmp: character -> character -> int

  val chars_from_int: int -> character list
  val char_from_int: int -> character
  val char_to_int: character -> int

  val list_from_string: string -> character list
  val list_to_string: character list -> string
end

module Utf16 : Character with type character = Unsigned.UInt16.t = struct
  type character = Unsigned.UInt16.t
  let cmp (l: character) (r: character): int = Unsigned.UInt16.compare l r

  let chars_from_int (code: int) : character list = 
    if code > 0xFFFF then
      (let shifted = (code - 0x10000) in
      let high = (shifted / 0x400) + 0xd800 in
      let low = (shifted mod 0x400) + 0xdc00 in
      (Unsigned.UInt16.of_int high) :: (Unsigned.UInt16.of_int low) :: [])
    else
      (Unsigned.UInt16.of_int code) :: []

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
      | h :: l :: t when Utf8Utils.is_high_surrogate h && Utf8Utils.is_low_surrogate l -> (
        let i = 0x10000 + (h - 0xd800)*0x400 + (l - 0xdc00) in
        assert (Utf8Utils.is_normal i);
        Buffer.add_utf_8_uchar b (Uchar.of_int i);
        iter t
      )
      | h :: t when Utf8Utils.is_normal h -> Buffer.add_utf_8_uchar b (Uchar.of_int h); iter t
      | _ :: t -> Buffer.add_utf_8_uchar b (Uchar.of_int 0xFFFD); iter t
      | [] -> ()
    in
    iter (List.map Unsigned.UInt16.to_int str);
    Buffer.contents b 
end

module Unicode : Character with type character = int = struct
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
          Buffer.add_utf_8_uchar b Utf8Utils.replacement_uchar
      ) str;
      Buffer.contents b 
end