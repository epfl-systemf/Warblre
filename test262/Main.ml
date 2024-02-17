open Warblre.Extracted.Patterns

let input = "dump.json"

let reduce_left f ls = match ls with
  | h :: t -> List.fold_left f h t
  | _ -> failwith "Cannot reduce empty list"

  (* let string_to_list str = List.init (String.length str) (String.get str)
  let list_to_string ls = String.init (List.length ls) (List.nth ls) *)

let find_field ls name = let (_, r) = List.find (fun (n, _) -> String.equal n name) ls in r

let json_to_regex (json: (string * Yojson.Safe.t) list): Warblre.Extracted.Frontend.coq_RegExpInstance =
  Yojson.Safe.(
    let rec iter (json: Yojson.Safe.t) = (match json with
    | `Assoc (("type", `String "Char") :: ("value", `String ".") :: ("kind", `String "meta") :: ("symbol", `String ".") :: ("codePoint", `Null) :: []) -> Dot
    | `Assoc (("type", `String "Alternative") :: ("expressions", `List expressions) :: _) -> expressions |> List.map iter |> reduce_left (fun l r -> Seq (l, r))
    | `Assoc (("type", `String "Assertion") :: ("kind", `String "^") :: []) -> InputStart
    | `Assoc (("type", `String "Assertion") :: ("kind", `String "$") :: []) -> InputEnd
    | _ -> failwith (String.cat "Unsupported JSON regex: " (Yojson.Safe.show json)))
    in
    let string_to_flags str =
      Warblre.Extracted.Frontend.(
        {
          d = String.contains str 'd';
          g = String.contains str 'g';
          i = String.contains str 'i';
          m = String.contains str 'm';
          s = String.contains str 's';
          u = String.contains str 'u';
          v = String.contains str 'v';
          y = String.contains str 'y';
        })
    in
    match find_field json "body", find_field json "flags" with
    | ast, `String flags ->
        let ast = iter ast in
        let flags = string_to_flags flags in
        (match (Warblre.Extracted.Frontend.coq_RegExpInitialize ast flags) with
        | Success x -> x
        | Failure _ -> failwith "Compile error")
    | _ -> failwith "Invalid JSON regex")

let node_exec regex input = 
  let js = (String.concat "" ("console.log(JSON.stringify({..." :: regex :: ".exec(" :: (Yojson.Safe.pretty_to_string (`String input)) :: ")}))":: [])) in
  let out_file = Filename.temp_file "node" ".out.json" in
  let command = Filename.quote_command "node" ~stdout:out_file ("-e" :: js :: []) in
  if Sys.command command != 0 then
    Yojson.Safe.from_string "null"
  else
    Yojson.Safe.from_file out_file

let warblre_exec regex input: Yojson.Safe.t =
  let get_first ls = match ls with
  | (Some str) :: _ -> Warblre.Interop.utf16_to_string str
  | _ -> failwith "No such element"
  in

  Warblre.Extracted.(
    match Frontend.coq_RegExpExec regex (Warblre.Interop.string_to_utf16 input) with
    | Result.Success (Null _) -> Yojson.Safe.from_string "{}"
    | Result.Success (Exotic (a,_)) -> 
      `Assoc (("0", `String (get_first a.array)) :: ("index", `Int a.index) :: ("input", `String input) :: [])
    | Result.Failure f -> Yojson.Safe.from_string "null")

let () =
  Yojson.Safe.(
    match from_file input with
    | `List json ->
      json
        |> List.iter (fun (instance: t) ->
            match instance with
            | `Assoc fields ->
              (match find_field fields "string", find_field fields "ast", find_field fields "input" with
              | `String str, `Assoc ast, `String input ->
                  let regex = (json_to_regex ast) in
                  let node_res = node_exec str input in
                  let warblre_res = warblre_exec regex input in
                  if Bool.not (Yojson.Safe.equal node_res warblre_res) then (
                    Printf.printf "regex : %s\n" (pretty_to_string (`String str));
                    Printf.printf "input : %s (%d)\n" (pretty_to_string (`String input)) (String.length input);
                    Printf.printf "node  : %s\n" (pretty_to_string (node_res));
                    Printf.printf "warblre: %s\n" (pretty_to_string (warblre_res)))
              | _ -> failwith "Level 1 should have fields 'string', 'ast' and 'flags'")
            | _ -> failwith "Level 1 should be an assoc")
    | _ -> failwith "Level 0 should be a list"
  )