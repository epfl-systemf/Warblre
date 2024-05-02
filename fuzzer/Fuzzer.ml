open Warblre.Engines
open Warblre.Printers

(* the different frontend functions we can test *)
type frontend_function =
  | Exec
  (* | Search
  | Test
  | Match
  | MatchAll *)

(** * Fuzzer parameters  *)

(* We restrict ourselves to a small alphabet
   with a sharp (#) to test word boundaries
*)
let alphabet : char list = ['#'; 'a'; 'b']

(* maximum bound for counted repetition *)
let counted_quantifiers_bound = 10

(* maximum string length *)
let max_string_length = 100

(* maximum regex AST depth *)
let max_regex_depth = 20

(** * Calling the Node Matcher (V8 backtracking)  *)

(* sending the type of frontend function to the JS matcher *)
let frontend_func (f:frontend_function) : string =
  match f with
  | Exec -> "exec"
  (* | Search -> "search"
  | Test -> "test"
  | Match -> "match"
  | MatchAll -> "matchAll" *)

(* geting the result of a command as a string *)
let string_of_command (command:string) : string =
 let tmp_file = Filename.temp_file "" ".txt" in
 let _ = Sys.command @@ command ^ " >" ^ tmp_file in
 let chan = open_in tmp_file in
 let output = ref "" in
 try
   while true do
     output := !output ^ input_line chan ^ "\n"
   done; !output
 with
   End_of_file ->
   close_in chan;
   !output

module Fuzzer (P: EngineParameters) (S: Warblre.Encoding.StringLike with type t := P.string) = struct
  open Warblre
  open Warblre.Extracted.Patterns
  open Engine(P)
  open Printer(P)(S)
  open Js_of_ocaml


  let get_success (r: ('a, 'b) Extracted.Result.coq_Result) =
    match r with
    | Success x -> x
    | Failure Extracted.MatchError.OutOfFuel -> failwith "Failure: Out of Fuel"
    | Failure Extracted.MatchError.AssertionFailed -> failwith "Failure: Assertion"

  let get_success_compile (r: ('a, 'b) Extracted.Result.coq_Result) =
    match r with
    | Success x -> x
    | Failure _ -> failwith "Compile Error"

  (* getting the Node result as a string, with a timeout in case of exponential complexity *)
  (* when the result is None, a Timeout occurred *)
  class type ['a] js_pair = object
    method first : 'a Js.readonly_prop
    method second : 'a Js.readonly_prop
  end

  let pair_to_tuple (p: int js_pair Js.t): ('a * 'a) = 
    (p##.first, p##.second)

  class type repacked_result = object
    method index : int Js.readonly_prop
    method groups : Js.js_string Js.t Js.optdef Js.js_array Js.t Js.readonly_prop
    method indices : int js_pair Js.t Js.optdef Js.js_array Js.t Js.optdef Js.readonly_prop
  end

  let repacked_result_to_result (reg: (character, string) Extracted.RegExpInstance.coq_type) (input: string) (r: repacked_result Js.t Js.opt): (character, string) Extracted.execResult =
    let to_mapped_option (type a b) (f: a -> b) (o: a Js.optdef): b option = Js.Optdef.to_option (Js.Optdef.map o f) in
    let to_mapped_list (type a b) (f: a -> b) (a: a Js.js_array Js.t): b list = List.map f (Array.to_list (Js.to_array a)) in
    let to_list = to_mapped_list (fun x -> x) in
    let to_string str = (S.of_string (Js.to_string str)) in
    match Js.Opt.to_option r with
    | None -> Null reg
    | Some r ->
        let exotic: (character, string) Extracted.ExecArrayExotic.coq_type = Extracted.ExecArrayExotic.({
          index = r##.index;
          input = input;
          array = to_mapped_list (to_mapped_option to_string) (r##.groups);
          groups = None; 
          indices_array = to_mapped_option (to_mapped_list (to_mapped_option pair_to_tuple)) (r##.indices);
          indices_groups = None;
        }) in
        Exotic (exotic, reg)

  (* external exec_result_pretty_print : Js.match_result_handle Js.t Js.opt -> ocaml_string = "exec_result_pretty_print" *)
  external exec_result_repack : Js.match_result_handle Js.t Js.opt -> repacked_result Js.t Js.opt = "exec_result_repack"

  let get_js_result (regex: (character, string) coq_Regex) (flags: Extracted.RegExpFlags.coq_type) (lastindex: int) (str: ocaml_string) (f: frontend_function): ocaml_string =
    let regex_string = regex_to_string ~delimited:false ~strict:true regex in
    let flags_string = flags_to_string flags in
    let js_regex = new%js Js.regExp_withFlags (Js.bytestring regex_string) (Js.string flags_string) in
    js_regex##.lastIndex := lastindex;
    match f with
    | Exec ->
        let instance = get_success_compile (initialize regex flags) in
        let result_js = js_regex##exec (Js.bytestring str) in
        let result_repacked = exec_result_repack result_js in
        let result = repacked_result_to_result instance (S.of_string str) result_repacked in
        String.trim (exec_result_to_string ~pretty:false result)

  (** * Calling the Reference Implementation *)
  (* exec *)
  let reference_exec (r: (character, string) Extracted.RegExpInstance.coq_type) (str) : ocaml_string =
    let res = get_success (exec r str) in
    exec_result_to_string ~pretty:false res


  let get_reference_result (regex: (character, string) coq_Regex) (flags: Extracted.RegExpFlags.coq_type) (index: int) (str: ocaml_string) (f: frontend_function) : ocaml_string =
    let instance = get_success_compile (initialize regex flags) in
    let instance = setLastIndex instance index in
    let list_input = S.of_string str in
    match f with
    | Exec -> String.trim (reference_exec instance list_input)
    (* | Search -> Some (reference_search instance (Obj.magic list_input))
    | Test -> Some (reference_test instance (Obj.magic list_input))
    | Match -> Some (reference_match instance (Obj.magic list_input))
    | MatchAll -> Some (reference_matchall instance (Obj.magic list_input)) *)



  (** * Comparing 2 engine results *)

  (* calling the two engines and failing if they disagree on the result *)
  let compare_engines ?(skip=false) (regex: (character, string) coq_Regex) (flags: Extracted.RegExpFlags.coq_type) (index: int) (str: ocaml_string) (f: frontend_function) : unit =
    let sep = String.init 100 (fun _ -> '-') in
    Printf.printf "\027[36mJS Regex:\027[0m %s\n" (regex_to_string regex);
    Printf.printf "\027[36mString:\027[0m \"%s\"\n%!" str;
    Printf.printf "\027[36mLastIndex:\027[0m \"%s\"\n%!" (string_of_int index);
    Printf.printf "\027[36mFlags:\027[0m \"%s\"\n%!" (flags_to_string flags);
    Printf.printf "\027[36mFunction:\027[0m \"%s\"\n%!" (frontend_func f);
    Printf.printf "\027[91m%s\027[0m\n" sep;
    Printf.printf "\027[35mIrregexp (node) result:\027[0m\n%!";
    let node_result = get_js_result regex flags index str f in
    Printf.printf "%s\n" node_result;
    Printf.printf "\027[91m%s\027[0m\n" sep;
    (* TODO: Ideally, the reference implementation should be run with a timeout in case the runtime explodes.
        A setup as in
        https://github.com/janestreet/async/blob/master/example/timeouts.ml might allow to do just that.
    *)
    Printf.printf "\027[35mWarblre result:\027[0m\n\n%!";
    let ref_result = get_reference_result regex flags index str f in
    Printf.printf "%s\n" ref_result;
    (* The outputs are compared in string format;
        A better (but more complicated) approach would be to compare the generated
        JavaScript objects.
    *)
    if (String.compare node_result ref_result != 0) then
      failwith "Outputs differ!"

  (** * Generating random regexes *)

  let cchar (c: char): (character, string) coq_Regex = Char (P.Character.from_numeric_value (Char.code c))

  let random_char () : char =
    let idx = Random.int (List.length alphabet) in
    List.nth alphabet idx

  let random_qp () : coq_QuantifierPrefix =
    match (Random.int 6) with
    | 0 -> Star
    | 1 -> Plus
    | 2 -> Question
    | 3 -> let rep = Random.int counted_quantifiers_bound in
          RepExact(rep)
    | 4 -> let rep = Random.int counted_quantifiers_bound in
          RepPartialRange(rep)
    | 5 -> let minrep = Random.int counted_quantifiers_bound in
          let maxrep = minrep + Random.int counted_quantifiers_bound in
          RepRange(minrep, maxrep)
    | _ -> failwith "random range error"

  let random_quant () : coq_Quantifier =
    let qp = random_qp () in
    if (Random.bool ()) then Greedy qp else Lazy qp

  let random_char_ranges () : (character, string) coq_ClassRanges =
    let sc c = SourceCharacter (P.Character.from_numeric_value (Char.code c)) in
    List.fold_left (fun current _: (character, string) coq_ClassRanges ->
      if Random.bool() then
        let c = random_char() in
        ClassAtomCR (sc c, current)
      else
        let c1 = random_char() in
        let c2 = random_char() in
        let cs = if c1 <= c2 then (c1, c2) else (c2, c1) in
        RangeCR (sc (fst cs), sc (snd cs), current)
    ) EmptyCR (List.init (Random.int 3) (fun x -> x))

  (* We generate regexes in two steps:
        1.  Random AST are generated, using a ticket system (more tickets = more chances of being generated), 
            where backreferences are all set to 0 (an invalid backref index)
        2.  Backreferences are replaced by indices between 1 and the maximum group index (selected at random).
            If the regex contains no group, backreferences are replaced by the empty regex.
  *)

  (* Table used to generate regex without children (i.e. leafs of the AST) *)
  let ticketTableNonRec: (int * (unit -> (character, string) coq_Regex)) list = [
    ( 1, fun _ -> Empty);
    ( 1, fun _: (character, string) coq_Regex ->
        let r = random_char_ranges () in
        let cc: (character, string) coq_CharClass = if Random.bool() then NoninvertedCC (r) else InvertedCC(r) in
        CharacterClass (cc)
    ); 
    ( 3, fun _ -> let c = random_char() in cchar(c));
    ( 1, fun _ -> AtomEsc (DecimalEsc 0));
    ( 1, fun _ -> Dot);
  ]

  let ticketTableRec: (int * (int -> (int -> (character, string) coq_Regex) -> (character, string) coq_Regex)) list = [
    ( 3, fun depth random_ast -> 
          let r1 = random_ast (depth-1) in
          let r2 = random_ast (depth-1) in
          Disjunction (r1, r2)
    );
    ( 5, fun depth random_ast -> 
          let r1 = random_ast (depth-1) in
          let r2 = random_ast (depth-1) in
          Seq (r1, r2)
    );
    ( 2, fun depth random_ast ->
          let r1 = random_ast (depth-1) in
          let quant = random_quant () in
          Quantified (r1, quant)
    );
    ( 2, fun depth random_ast ->
          let r1 = random_ast (depth-1) in
          Group (None, r1)       (* TODO: generate named groups *)
    );
    ( 1, fun depth random_ast ->
          let r1 = random_ast (depth-1) in
          Lookahead (r1)
    );
    ( 1, fun depth random_ast ->
          let r1 = random_ast (depth-1) in
          NegativeLookahead (r1)
    );
    ( 1, fun depth random_ast ->
            let r1 = random_ast (depth-1) in
            Lookbehind (r1)
    );
    ( 1, fun depth random_ast ->
            let r1 = random_ast (depth-1) in
            NegativeLookbehind (r1)
    );
  ]

  module Lookup = Map.Make (Int)
  let build_lookup (ls: (int * 'a) list): 'a Lookup.t =
      snd (List.fold_left ( fun acc p ->
        let (current, lookup) = acc in
        let (tickets, v) = p in
        let lookup = ref lookup in
        for i = 1 to tickets do
          lookup := Lookup.add (current + i - 1) v !lookup
        done;
        (current + tickets, !lookup)
      ) (0, Lookup.empty) ls)

  let base_lookup = build_lookup ticketTableNonRec
  let full_lookup = build_lookup (List.concat [ 
    List.map (fun p -> let (t, f) = p in (t, fun _ _ -> f ())) ticketTableNonRec ; 
    ticketTableRec
    ])

  let rec random_ast (depth:int) : (character, string) coq_Regex =
    if (depth = 0) then
      (* The regex cannot have further children -> use the "childless" table *)
      let rand = Random.int (Lookup.cardinal base_lookup) in
      let gen = Lookup.find rand base_lookup in
      gen ()
    else
      (* Use the full table *)
      let rand = Random.int (Lookup.cardinal full_lookup) in
      let gen = Lookup.find rand full_lookup in
      gen depth random_ast

  (* Replace each backreference number with a legal one, between 1 and the maximum group id  *)
  let rec fill_backref (r: (character, string) coq_Regex) (maxgroup: int) : (character, string) coq_Regex =
    match r with
    | Empty | Char _ | Dot| CharacterClass _ -> r
    | AtomEsc (DecimalEsc _) ->
        if (maxgroup = 0) then Empty
        else let groupid = (Random.int maxgroup) + 1 in
          AtomEsc (DecimalEsc groupid)
    | AtomEsc _ -> r
    | Disjunction (r1,r2) -> Disjunction (fill_backref r1 maxgroup, fill_backref r2 maxgroup)
    | Quantified (r1,quant) -> Quantified (fill_backref r1 maxgroup, quant)
    | Seq (r1,r2) -> Seq (fill_backref r1 maxgroup, fill_backref r2 maxgroup)
    | Group (nameop, r1) -> Group (nameop, fill_backref r1 maxgroup)
    | InputStart | InputEnd | WordBoundary | NotWordBoundary -> r
    | Lookahead (r1) -> Lookahead (fill_backref r1 maxgroup)
    | NegativeLookahead (r1) -> NegativeLookahead (fill_backref r1 maxgroup)
    | Lookbehind (r1) -> Lookbehind (fill_backref r1 maxgroup)
    | NegativeLookbehind (r1) -> NegativeLookbehind (fill_backref r1 maxgroup)

  (* Generate an AST then fills the backreferences numbers *)
  let random_regex (): (character, string) coq_Regex =
    let ast = random_ast (Random.int max_regex_depth) in
    let maxgroup = countGroups ast in
    fill_backref ast maxgroup

  (* Generate random flags *)
  let random_flags () : Extracted.RegExpFlags.coq_type =
    { d = Random.bool();
      g = Random.bool();
      i = Random.bool();
      m = Random.bool();
      s = Random.bool();
      u = ();
      y = Random.bool();
    }

  (* does not generate matchall if there is no global flag *)
  let random_frontend (glob: bool) : frontend_function =
    match (Random.int(1)) with
    | 0 -> Exec
    (* | 1 -> Search
    | 2 -> Test
    | 3 -> Match
    | 4 -> MatchAll *)
    | _ -> failwith "random range error"

  (** * Creating Random Strings  *)

  let random_string () : ocaml_string =
    let size = (Random.int max_string_length) in
    String.init size (fun _ -> random_char())


  (** * Differential Fuzzer  *)

  let fuzzer ?(start_from=0) (max_tests: int) : unit =
    let iter_witdth = 8 in
    let sep = String.init ((100 - iter_witdth - 2) / 2) (fun _ -> '=') in
    for i = 0 to max_tests do
      let rgx = random_regex () in
      let flags = random_flags () in
      let lastindex = Random.int(max_string_length) in
      let str = random_string () in
      let f = random_frontend (flags.g) in
      if (i >= start_from) then
        (Printf.printf "\027[91m%s %*d %s\027[0m\n" sep iter_witdth i sep;
        compare_engines rgx flags lastindex str f)
    done;
    Printf.printf "\027[91m%s\027[0m\n" (String.init 100 (fun _ -> '='))


end

open Fuzzer(UnicodeParameters)(Warblre.Encoding.Utf16StringLike)
let () =
  let start_from = 0 in
  let test_count: int = 100 in
  let user_seed: int option = Some 89809344 in
  let seed: int = (Option.value (Option.map (fun v _ -> v) user_seed) ~default:(fun _ -> Random.int (1073741823))) () in
  Printf.printf "\027[91mSeed is %d. Starting at test %d.\027[0m\n" seed start_from;
  Random.init seed;
  fuzzer ~start_from:start_from test_count;
  Printf.printf "\027[91mFinished %d tests.\027[0m\n" test_count;