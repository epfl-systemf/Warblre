module Common = struct
  let parse_hex ls =
    int_of_string ("0x" ^ (String.concat "" (List.map (fun c -> String.make 1 c) ls)))
end