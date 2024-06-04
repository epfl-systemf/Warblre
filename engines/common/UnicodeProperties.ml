(* Disables properties, for non-unicode mode. *)
module NoProperty = struct
  type t = |
  let equal (_: t) (_: t) = false
  let code_points (_: t) = failwith "How was the empty type instanciated?"
end

(* We did not implement all properties, but did include one ("Alphabetic") as a proof of concept *)
module UnicodeProperty = struct
  type t = 
  | Alphabetic

  let equal x y = match x, y with
  | Alphabetic, Alphabetic -> true
end