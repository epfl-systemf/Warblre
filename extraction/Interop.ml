module Common = struct
  let parse_hex ls =
    int_of_string ("0x" ^ (String.concat "" (List.map (fun c -> String.make 1 c) ls)))
end

module Utf16 = struct
  include Encoding.Utf16

  let code_points_to_string (c: Encoding.codepoint list): character list = List.flatten (List.map chars_from_int c)

  let to_upper_case (c: Encoding.codepoint): Encoding.codepoint list =
    if Uchar.is_valid c then
      match Uucp.Case.Map.to_upper (Uchar.of_int c) with
        | `Self -> c :: []
        | `Uchars ls -> List.map Uchar.to_int ls
    else c :: []
end

module Unicode = struct
  include Encoding.Unicode

  let case_fold (c: character): character = 
    if (Uchar.is_valid c) then
      match Uucp.Case.Fold.fold (Uchar.of_int c) with
        | `Self -> c
        | `Uchars (cp :: []) -> Uchar.to_int cp
        | `Uchars _ -> c
    else c
end