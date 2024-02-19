open Warblre.Extracted.Patterns

let input = "dump.json"
let max_failures_count = 10

let find_field ls name = let (_, r) = List.find (fun (n, _) -> String.equal n name) ls in r

let input_to_string input = String.concat "," (List.map (fun c -> Int.to_string (Warblre.Interop.char_to_int c)) input)

let node_exec regex flags input index = 
  let js_input = input_to_string input in
  let js = Printf.sprintf {|
    const regex = /%s/%s;
    regex.lastIndex = %d;
    const input_array = [%s];
    var enc = new TextDecoder("utf-16");
    const input = enc.decode(new Uint16Array(input_array));
    console.log(JSON.stringify({...regex.exec(input)}));
  |} regex flags index js_input in
  (* Printf.printf "%s\n" js; *)
  let out_file = Filename.temp_file "node" ".out.json" in
  let command = Filename.quote_command "node" ~stdout:out_file ("-e" :: js :: []) in
  let res_code = Sys.command command in
  if res_code != 0 then
    Yojson.Safe.from_string "null"
  else
    Yojson.Safe.from_file out_file

let warblre_exec regex input: Yojson.Safe.t =
  let format_groups ls: (string * Yojson.Safe.t) list =
    let rec iter ls i =
      match ls with
      | (Some str) :: t -> (Int.to_string i, `String (Warblre.Interop.utf16_to_string str)) :: (iter t (i+1))
      | None :: t -> iter t (i+1)
      | [] -> []
    in
    iter ls 0
  in

  Warblre.Extracted.(
    match Frontend.coq_RegExpExec regex input with
    | Result.Success (Null _) -> Yojson.Safe.from_string "{}"
    | Result.Success (Exotic (a,_)) -> 
      `Assoc (
        (format_groups a.array) @
        (("index", `Int a.index) :: ("input", `String (Warblre.Interop.utf16_to_string input)) :: []))
    | Result.Failure f -> Yojson.Safe.from_string "\"FAILURE\"")

let () =
  Yojson.Safe.(
    match from_file input with
    | `List json ->
      let failures_count = ref 0 in
      json
        |> List.iteri (fun (i: int) (instance: t) ->
            match instance with
            | `Assoc fields ->
              (match find_field fields "pattern", find_field fields "flags", find_field fields "index", find_field fields "ast", find_field fields "input" with
              | `String str_pattern, `String str_flags, `Int index, `Assoc ast, `List raw_input ->
                  let input = List.map (fun e -> match e with
                    | `Int i -> Warblre.Interop.char_of_int i
                    | _ -> failwith (String.cat "Invalid element in input string: " (pretty_to_string e))
                  ) raw_input in
                  (try
                    let node_res = node_exec str_pattern str_flags input index in
                    let regex = (RegexpTree.json_to_regex ast index) in
                    let warblre_res = warblre_exec regex input in
                    if Bool.not (Yojson.Safe.equal node_res warblre_res) then (
                      failures_count := !failures_count + 1;
                      Printf.printf "FAILED [%d]: engines do not agree.\n" i;
                      Printf.printf "\tregex     : %s / \"%s\" @ %d\n" (pretty_to_string (`String str_pattern)) str_flags index;
                      Printf.printf "\traw input : [%s]\n" (input_to_string input);
                      Printf.printf "\tinput     : \"%s\"\n" (Warblre.Interop.utf16_to_string input);
                      Printf.printf "\tnode      : %s\n" (pretty_to_string (node_res));
                      Printf.printf "\textracted : %s\n%!" (pretty_to_string (warblre_res)))
                    else Printf.printf "SUCCESS [%d]: %s / \"%s\" | %s @ %d\n%!" i (Warblre.Interop.utf16_to_string input) (pretty_to_string (`String str_pattern)) str_flags index
                  with Failure msg -> (
                    failures_count := !failures_count + 1;
                    Printf.printf "FAILED [%d]: an error occured.\n" i;
                    Printf.printf "\tregex     : %s / %s\n" (pretty_to_string (`String str_pattern)) str_flags;
                    Printf.printf "\traw input : [%s]\n" (input_to_string input));
                    Printf.printf "\tinput     : \"%s\"\n" (Warblre.Interop.utf16_to_string input);
                    Printf.printf "\tmessage   : %s\n%!" msg);
                  if !failures_count >= max_failures_count then failwith "Maximal number of failures reached"
              | _ -> failwith "Level 1 should have fields 'pattern', 'flags', 'index', 'ast' and 'flags'")
            | _ -> failwith "Level 1 should be an assoc")
    | _ -> failwith "Level 0 should be a list"
  )