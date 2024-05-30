(* Miscellaneous utilities used during extraction. *)

(* Parse a sequence of hex digits into an integer. *)
let parse_hex ls =
  Host.of_int (int_of_string ("0x" ^ (String.concat "" (List.map (fun c -> String.make 1 c) ls))))


type ('a, 'b) result = 'a
let success (type a) (v: a): a = v
let failure (type a b) (_: a): b = failwith "Success.failure"

(*
   A function which should never be used by the extracted code.
   This is used as the extraction target of functions which should not be used
   (because all of their call-sites have themselves been replaced by an OCaml constants),
   yet still appear in the extracted OCaml code, because they are recursive.

   In such cases, extracting to this constant ensures that they are indeed never used.
*)
let erased _ = failwith "This function should have disappeared at extraction..."