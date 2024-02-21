open Warblre.Extracted.Patterns

let find_field ls name = let (_, r) = List.find (fun (n, _) -> String.equal n name) ls in r

let input_to_string input = String.concat "," (List.map (fun c -> Int.to_string (Warblre.Interop.char_to_int c)) input)

let timed f =
  let t0 = Sys.time() in
  let r = f () in
  let t1 = Sys.time() in
  (r, t1 -. t0)

let stream_file name: string Seq.t =
  let ic = open_in name in
  let try_read () = try Some (input_line ic) with End_of_file -> None in
  let iter acc = 
    match try_read () with
    | Some s -> Some ((s, ()))
    | None -> close_in ic; None
  in
  Seq.unfold iter ()

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
  let out_file = Filename.temp_file "node_" ".out.json" in
  let command = Filename.quote_command "node" ~stdout:out_file ("-e" :: js :: []) in
  let res_code = Sys.command command in
  if res_code != 0 then
    Yojson.Safe.from_string "\"Node --- FAILURE\""
  else
    Yojson.Safe.from_file out_file

let warblre_exec regex input: Yojson.Safe.t =
  let format_groups_numbered ls: (string * Yojson.Safe.t) list =
    let rec iter ls i =
      match ls with
      | (Some str) :: t -> (Int.to_string i, `String (Warblre.Interop.utf16_to_string str)) :: (iter t (i+1))
      | None :: t -> iter t (i+1)
      | [] -> []
    in
    iter ls 0
  in
  let format_groups_named (groups: Warblre.Extracted.Frontend.groups_map): Yojson.Safe.t =
    let rec iter ls =
      match ls with
      | (name, Some str) :: t -> (name, `String (Warblre.Interop.utf16_to_string str)) :: (iter t)
      | (name, None) :: t -> iter t
      | [] -> []
    in
    `Assoc (iter groups)
  in

  let maybe_add_groups (current: (string * Yojson.Safe.t) list) (groups: Warblre.Extracted.Frontend.groups_map option): (string * Yojson.Safe.t) list =
    match groups with
    | Some groups -> List.append current (("groups", format_groups_named groups) :: [])
    | None -> current
  in

  Warblre.Extracted.(
    match Frontend.coq_RegExpExec regex input with
    | Result.Success (Null _) -> Yojson.Safe.from_string "{}"
    | Result.Success (Exotic (a,_)) -> 
      let base = (format_groups_numbered a.array) @
        (("index", `Int a.index) :: ("input", `String (Warblre.Interop.utf16_to_string input)) :: [])
      in
      let extended = maybe_add_groups base a.groups in
      `Assoc extended
    | Result.Failure f -> Yojson.Safe.from_string "\"Extracted --- FAILURE\"")

let filter_tests filters (tests: (int * Yojson.Safe.t) Seq.t) =
  List.fold_left (fun tests filter ->
    Seq.filter filter tests  
  ) tests filters

module Filters = struct
  let only ids: (int * Yojson.Safe.t) -> bool =
    let module S = Set.Make(Int) in
    let only = List.fold_left (fun set elem -> S.add elem set) S.empty ids in
    fun (i, _) -> S.mem i only

  let exclude ids: (int * Yojson.Safe.t) -> bool =
    let module S = Set.Make(Int) in
    let excluded = List.fold_left (fun set elem -> S.add elem set) S.empty ids in
    fun (i, _) -> Bool.not (S.mem i excluded)

  let modulo m r: (int * Yojson.Safe.t) -> bool =
    fun (i, _) -> i mod m = r
end

let run input filters ?(display=false) ?(max_failures_count=Int.max_int) ?(log_success=false) () =
  Yojson.Safe.(
    let start_time = Sys.time () in
    let test_count = ref 0 in
    let failures_count = ref 0 in
    let max_runtime = ref (Float.min_float) in

    (stream_file input
      |> Seq.map from_string
      |> Seq.zip (Seq.ints 1)
      |> filter_tests filters
      |> (Seq.iter (fun (i, instance) ->
            test_count := !test_count + 1;
            match instance with
            | `Assoc fields ->
              (match find_field fields "pattern", find_field fields "flags", find_field fields "index", find_field fields "ast", find_field fields "input" with
              | `String str_pattern, `String str_flags, `Int index, `Assoc ast, `List raw_input ->
                  let input = List.map (fun e -> match e with
                    | `Int i -> Warblre.Interop.char_of_int i
                    | _ -> failwith (String.cat "Invalid element in input string: " (pretty_to_string e))
                  ) raw_input in
                  (if display then Printf.printf "Running test %d...\r%!" i);
                  (try
                    Gc.full_major ();
                    let (node_res, node_time) = timed (fun _ -> node_exec str_pattern str_flags input index) in
                    let regex = RegexpTree.json_to_regex ast index in
                    let (warblre_res, warblre_time) = timed (fun _ -> warblre_exec regex input) in
                    if (warblre_time > !max_runtime) then max_runtime := warblre_time;
                    if Bool.not (Yojson.Safe.equal node_res warblre_res) then (
                      failures_count := !failures_count + 1;
                      ANSITerminal.erase Below;
                      Printf.printf "FAILED [%d]: engines do not agree.\n" i;
                      Printf.printf "\tregex     : %s / \"%s\" @ %d\n" (pretty_to_string (`String str_pattern)) str_flags index;
                      Printf.printf "\traw input : [%s]\n" (input_to_string input);
                      Printf.printf "\tinput     : \"%s\"\n" (Warblre.Interop.utf16_to_string input);
                      Printf.printf "\tnode      : %s\n" (pretty_to_string (node_res));
                      Printf.printf "\t\ttime : %fs\n" node_time;
                      Printf.printf "\textracted : %s\n%!" (pretty_to_string (warblre_res));
                      Printf.printf "\t\ttime : %fs\n" warblre_time)
                    else if log_success then (
                      ANSITerminal.erase Below;
                      Printf.printf "Success [%d]: node %fs; extracted %fs.\n" i node_time warblre_time)
                  with Failure msg | Invalid_argument msg | Yojson.Json_error msg -> (
                    failures_count := !failures_count + 1;
                    ANSITerminal.erase Below;
                    Printf.printf "FAILED [%d]: an error occured.\n" i;
                    Printf.printf "\tregex     : %s / %s\n" (pretty_to_string (`String str_pattern)) str_flags;
                    Printf.printf "\traw input : [%s]\n" (input_to_string input));
                    Printf.printf "\tinput     : \"%s\"\n" (Warblre.Interop.utf16_to_string input);
                    Printf.printf "\tmessage   : %s\n%!" msg);
                  if !failures_count >= max_failures_count then failwith "Maximal number of failures reached"
              | _ -> failwith "Level 1 should have fields 'pattern', 'flags', 'index', 'ast' and 'flags'")
            | _ -> failwith "Level 1 should be an assoc")));
    ANSITerminal.erase Below;
    Printf.printf "Summary:\n";
    Printf.printf "\tFailures           : %d/%d\n" (!failures_count) (!test_count);
    Printf.printf "\tTotal runtime      : %fs\n" (Sys.time () -. start_time);
    Printf.printf "\tHighest runtime    : %fs\n" (!max_runtime))


let () =
  Printexc.record_backtrace true;
  let input_file = if Array.length Sys.argv > 1 then Sys.argv.(1) else "dump.json" in
  let (modulus, offset) = if Array.length Sys.argv > 3 then (int_of_string Sys.argv.(2), int_of_string Sys.argv.(3)) else (0, 0) in
  let filters = Filters.(
    []) 
  in
  let filters = if modulus != 0
    then (Printf.printf "Running with modulus=%d and offset=%d\n%!" modulus offset; (Filters.modulo modulus offset) :: filters)
    else (Printf.printf "Running all tests.\n%!"; filters)
  in
  run input_file filters ~display:false ~log_success:true ()