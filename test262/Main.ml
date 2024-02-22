open Warblre.Extracted.Patterns

let find_field ls name = let (_, r) = List.find (fun (n, _) -> String.equal n name) ls in r

let input_to_string input = String.concat "," (List.map (fun c -> Int.to_string (Warblre.Interop.char_to_int c)) input)

let time _: float = Unix.gettimeofday ()

let timed f =
  let t0 = time () in
  let r = f () in
  let t1 = time () in
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

let read_whole_file filename =
  let ch = open_in filename in
  let s = really_input_string ch (in_channel_length ch) in
  close_in ch;
  s

let node_exec regex flags input index: Yojson.Safe.t = 
  let js_input = input_to_string input in
  let js = Printf.sprintf {|
    function replacer(key, value) {
      if (typeof value === "string") {
        const input = new Array;
        for (let i = 0; i < value.length; i++) {
            let c = value.charCodeAt(i);
            input.push(c);
        }
        return input;
      }
      return value;
    }

    const regex = /%s/%s;
    regex.lastIndex = %d;
    const input_array = [%s];
    const dec = new TextDecoder("utf-16");
    const input = dec.decode(new Uint16Array(input_array));
    console.log(JSON.stringify({...regex.exec(input)}, replacer, 1));
  |} regex flags index js_input in
  let out_file = Filename.temp_file "node_" ".out.json" in
  let command = Filename.quote_command "node" ~stdout:out_file ("-e" :: js :: []) in
  let res_code = Sys.command command in
  if res_code != 0 then
    Yojson.Safe.from_string "\"Node --- FAILURE\""
  else
    Yojson.Safe.from_file out_file

let warblre_exec regex input: Yojson.Safe.t =
  let string_to_json str = `List (List.map (fun i -> `Int (Warblre.Interop.char_to_int i)) str) in
  (* let string_to_json str: Yojson.Safe.t = `List (List.map (fun i -> `Int i) (Warblre.Interop.clean_utf16 str)) in *)

  let format_groups_numbered ls: (string * Yojson.Safe.t) list =
    let rec iter ls i =
      match ls with
      | (Some str) :: t -> (Int.to_string i, string_to_json str) :: (iter t (i+1))
      | None :: t -> iter t (i+1)
      | [] -> []
    in
    iter ls 0
  in
  let format_groups_named (groups: Warblre.Extracted.Frontend.groups_map): Yojson.Safe.t =
    let rec iter ls =
      match ls with
      | (name, Some str) :: t -> (name, string_to_json str) :: (iter t)
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

  let input = Warblre.Interop.clean_utf16 input in
  match Warblre.Extracted.Frontend.coq_RegExpExec regex input with
  | Warblre.Extracted.Result.Success (Null _) -> Yojson.Safe.from_string "{}"
  | Warblre.Extracted.Result.Success (Exotic (a,_)) -> 
    let base = (format_groups_numbered a.array) @
      (("index", `Int a.index) :: ("input", string_to_json input) :: [])
    in
    let extended = maybe_add_groups base a.groups in
    `Assoc extended
  | Warblre.Extracted.Result.Failure f -> Yojson.Safe.from_string "\"Extracted --- FAILURE\""

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
    let start_time = time () in
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
                      Printf.printf "regex     : %s / \"%s\" @ %d\n" (pretty_to_string (`String str_pattern)) str_flags index;
                      Printf.printf "raw input : [%s]\n" (input_to_string input);
                      Printf.printf "input     : \"%s\"\n" (Warblre.Interop.utf16_to_string input);
                      Printf.printf "node      : %fs\n\"\"\"\n%s\n\"\"\"\n" node_time (pretty_to_string node_res);
                      Printf.printf "extracted : %fs\n\"\"\"\n%s\n\"\"\"\n\n%!" warblre_time (pretty_to_string warblre_res))
                    else if log_success then (
                      ANSITerminal.erase Below;
                      Printf.printf "Success [%d]: node %fs; extracted %fs.\n" i node_time warblre_time)
                  with Failure msg | Invalid_argument msg  -> ( (*| Yojson.Json_error msg -> ( *)
                    failures_count := !failures_count + 1;
                    ANSITerminal.erase Below;
                    Printf.printf "FAILED [%d]: an error occured.\n" i;
                    Printf.printf "regex     : %s / %s\n" (pretty_to_string (`String str_pattern)) str_flags;
                    Printf.printf "raw input : [%s]\n" (input_to_string input));
                    Printf.printf "input     : \"%s\"\n" (Warblre.Interop.utf16_to_string input);
                    Printf.printf "message   : %s\n\n%!" msg);
                  if !failures_count >= max_failures_count then failwith "Maximal number of failures reached"
              | _ -> failwith "Level 1 should have fields 'pattern', 'flags', 'index', 'ast' and 'flags'")
            | _ -> failwith "Level 1 should be an assoc")));
    ANSITerminal.erase Below;
    Printf.printf "\nSummary:\n";
    Printf.printf "\tTests succeeded    : %d/%d\n" (!test_count - !failures_count) (!test_count);
    Printf.printf "\tTotal runtime      : %fs\n" (time () -. start_time);
    Printf.printf "\tHighest runtime    : %fs\n" (!max_runtime))


let () =
  Printexc.record_backtrace true;
  let input_file = if Array.length Sys.argv > 1 then Sys.argv.(1) else "../test262/dump.json" in
  let (modulus, offset) = if Array.length Sys.argv > 3 then (int_of_string Sys.argv.(2), int_of_string Sys.argv.(3)) else (0, 0) in
  let filters = Filters.(
    (* (only (1 :: [])) :: *)
    []) 
  in
  let filters = if modulus != 0
    then (Printf.printf "Running with modulus=%d and offset=%d\n%!" modulus offset; (Filters.modulo modulus offset) :: filters)
    else (Printf.printf "Running all tests.\n%!"; filters)
  in
  run input_file filters ~display:false ~log_success:true ()