open Warblre.Extracted.ECMA

let find_field ls name = let (_, r) = List.find (fun (n, _) -> String.equal n name) ls in r

let warblre_exec (type a) regex (input: a list) (p: a -> int) : Yojson.Safe.t =
  let string_to_json str = `Assoc (("data", `List (List.map (fun i -> `Int (p i)) str)) :: ("isString", `Bool true) :: []) in
  let make_exotic ls = `Assoc (("exotic", `Assoc ls) :: ("isExotic", `Bool true) :: []) in

  let format_list_optional (type a) (f: a -> Yojson.Safe.t) (ls: a option list): (string * Yojson.Safe.t) list =
    let rec iter ls i =
      match (ls: a option list) with
      | (Some v) :: t -> (Int.to_string i, f v) :: (iter t (i+1))
      | None :: t -> (Int.to_string i, `Null) :: (iter t (i+1))
      | [] -> []
    in
    iter ls 0
  in
  let format_map_optional (type a) f (ls: (string * a option) list): Yojson.Safe.t =
    let rec iter ls =
      match ls with
      | (name, Some v) :: t -> (name, f v) :: (iter t)
      | (name, None) :: t -> (name, `Null) :: iter t
      | [] -> []
    in
    `Assoc (iter ls)
  in

  let add current name value = List.append current ((name, value) :: []) in
  let add_maybe (type a) (current: (string * Yojson.Safe.t) list) (maybe: a option) name (f: a -> Yojson.Safe.t): (string * Yojson.Safe.t) list =
    let value = match maybe with
    | Some v -> f v
    | None -> `Null
    in
    add current name value
  in

  
  match coq_RegExpExec regex (Obj.magic input) with
  | Warblre.Extracted.Result.Success (Null regex_new) ->
    `Assoc (("lastIndex", `Int (regex_new.lastIndex) ) :: ("result", `Null) :: [])
  | Warblre.Extracted.Result.Success (Exotic (a, regex_new)) ->
    let res = (format_list_optional string_to_json (Obj.magic a.array)) @
      (("index", `Int a.index) :: ("input", string_to_json input) :: [])
    in
    let res = add_maybe res a.groups "groups" (format_map_optional (Obj.magic string_to_json)) in
    let res = (
      match a.indices_array with
      | None -> res
      | Some indices ->
        let format_indices (i, j) = `List (`Int i :: `Int j :: []) in
        let indices = format_list_optional format_indices indices in
        let indices = add_maybe indices a.indices_groups "groups" (format_map_optional format_indices) in
        add res "indices" (make_exotic indices))
    in
    `Assoc (("lastIndex", `Int (regex_new.lastIndex) ) :: ("result", make_exotic res) :: [])
  | Warblre.Extracted.Result.Failure f -> failwith "EXECUTION FAILURE"

let () =
  Printexc.record_backtrace true;
  if Array.length Sys.argv < 2 || Array.length Sys.argv > 3 then failwith "Incorrect number of arguments provided";
  let input = (Sys.argv.(1)) in
  let write_output out_str = (
    if Array.length Sys.argv > 2 then (
      let output = (Sys.argv.(2)) in
      let oc = open_out output in
      Printf.fprintf oc "%s" out_str;
      close_out oc)
    else (
      Printf.printf "%s\n" out_str
    ))
  in
  Yojson.Safe.(
    try (
      match from_file input with
      | `Assoc fields ->
        (match find_field fields "index", find_field fields "ast", find_field fields "input", find_field fields "unicode" with
        | `Int index, `Assoc ast, `List raw_input, `Bool unicode -> (

          let res = if Bool.not unicode then (
            let input = List.map (fun e -> match e with
              | `Int i -> Warblre.Interop.Utf16.char_of_int i
              | _ -> failwith (String.cat "Invalid element in input string: " (pretty_to_string e))
            ) raw_input in
            let input = Warblre.Interop.Utf16.clean_utf16 input in
            
            let regex = RegexpTree.Utf16.json_to_regex ast index in
            warblre_exec regex input Warblre.Interop.Utf16.char_to_int)

          else (
            let input = List.map (fun e -> match e with
              | `Int i -> Warblre.Interop.Unicode.char_of_int i
              | _ -> failwith (String.cat "Invalid element in input string: " (pretty_to_string e))
            ) raw_input in
            
            let regex = RegexpTree.Unicode.json_to_regex ast index in
            warblre_exec regex input Warblre.Interop.Unicode.char_to_int)
          in
          write_output (to_string res))


        | _ -> failwith "Failure: Level 1 is missing some fields.")
      | _ -> failwith "Failure: Level 1 should be an assoc.")
    with Failure msg | Invalid_argument msg | Yojson__Common.Json_error msg -> (
      write_output ("Failure: " ^ msg)))