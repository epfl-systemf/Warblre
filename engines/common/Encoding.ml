type codepoint = int

module UnicodeUtils = struct
  (* Unicode points are represented using int (rather than Uchar.t) as to represent invalid points *)
  type uchar = int

  let to_bytes (u: uchar) : char list =
    match u with
    | u when u < 0 -> assert false
    | u when u <= 0x007F -> Char.chr u :: []
    | u when u <= 0x07FF -> Char.chr (0xC0 lor (u lsr 6)) :: Char.chr (0x80 lor (u land 0x3F)) :: []
    | u when u <= 0xFFFF -> Char.chr (0xE0 lor (u lsr 12)) :: Char.chr (0x80 lor ((u lsr 6) land 0x3F)) :: Char.chr (0x80 lor (u land 0x3F)) :: []
    | u when u <= 0x10FFFF -> Char.chr (0xF0 lor (u lsr 18)) :: Char.chr (0x80 lor ((u lsr 12) land 0x3F)) :: Char.chr (0x80 lor ((u lsr 6) land 0x3F)) :: Char.chr (0x80 lor (u land 0x3F)) :: []
    | _ -> failwith "Int is to big for a unicode character!"

    
    let is_high_surrogate (c: uchar) = (0xd800 <= c) && (c <= 0xdbff)
    let is_low_surrogate (c: uchar) = (0xdc00 <= c) && (c <= 0xdfff)
    (* I.e. not a surrogate *)
    let is_normal (c: uchar) = (0x0000 <= c && c < 0xd800) || (0xe000 <= c)

    let replacement_char = Uchar.of_int 0xFFFD

    let to_utf16 (code: uchar) : int list = 
      if code > 0xFFFF then
        (let shifted = (code - 0x10000) in
        let high = (shifted / 0x400) + 0xd800 in
        let low = (shifted mod 0x400) + 0xdc00 in
        high :: low :: [])
      else
        code :: []
    let str_to_utf16 (c: uchar list): int list = List.flatten (List.map to_utf16 c)
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

module type StringLike = sig
  type t
  val to_string: t -> string
  val of_string: string -> t
end
