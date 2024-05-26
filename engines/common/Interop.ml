module Common = struct
  let parse_hex ls =
    Host.of_int (int_of_string ("0x" ^ (String.concat "" (List.map (fun c -> String.make 1 c) ls))))
end

type ('a, 'b) result = 'a
let success (type a) (v: a): a = v
let failure (type a b) (_: a): b = failwith "Success.failure"

let erased _ = failwith "This function should have disappeared at extraction..."