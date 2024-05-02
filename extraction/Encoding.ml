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

    let to_utf16 (code: uchar) : Unsigned.UInt16.t list = 
      if code > 0xFFFF then
        (let shifted = (code - 0x10000) in
        let high = (shifted / 0x400) + 0xd800 in
        let low = (shifted mod 0x400) + 0xdc00 in
        (Unsigned.UInt16.of_int high) :: (Unsigned.UInt16.of_int low) :: [])
      else
        (Unsigned.UInt16.of_int code) :: []
    let str_to_utf16 (c: uchar list): Unsigned.UInt16.t list = List.flatten (List.map to_utf16 c)
  
    let to_upper_case (c: uchar): int list =
      if Uchar.is_valid c then
        match Uucp.Case.Map.to_upper (Uchar.of_int c) with
          | `Self -> c :: []
          | `Uchars ls -> List.map Uchar.to_int ls
      else c :: []
      
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

  let chars_from_int = UnicodeUtils.to_utf16

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
      | h :: l :: t when UnicodeUtils.is_high_surrogate h && UnicodeUtils.is_low_surrogate l -> (
        let i = 0x10000 + (h - 0xd800)*0x400 + (l - 0xdc00) in
        assert (UnicodeUtils.is_normal i);
        Buffer.add_utf_8_uchar b (Uchar.of_int i);
        iter t
      )
      | h :: t when UnicodeUtils.is_normal h -> Buffer.add_utf_8_uchar b (Uchar.of_int h); iter t
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
          Buffer.add_utf_8_uchar b UnicodeUtils.replacement_char
      ) str;
      Buffer.contents b 
end



module type StringLike = sig
  type t
  val to_string: t -> string
  val of_string: string -> t
end

module Utf16StringLike : StringLike
  with type t = Utf16.character list
= struct
  type t = Utf16.character list
  let to_string = Utf16.list_to_string
  let of_string = Utf16.list_from_string
end