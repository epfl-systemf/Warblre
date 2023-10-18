module Ocaml_Map_Int = Map.Make(Int)
module Ocaml_Set_Int = Set.Make(Int)

let remove_all m s = Ocaml_Set_Int.fold Ocaml_Map_Int.remove s m