open Warblre_js.Engines
open Warblre_js.Printers

(* the different frontend functions we can test *)
type frontend_function =
  | Exec
  | Search
  | Test
  | Match
  | MatchAll

(** * Fuzzer parameters  *)

(* We restrict ourselves to a small alphabet
   with a sharp (#) to test word boundaries
*)
let alphabet : char list = ['#'; 'a'; 'b']

(* Potential names for named capture groups *)
let group_names: string list =
  "_1" ::
  "_2" ::
  "_3" ::
  "_4" ::
  "_5" ::
  "_6" ::
  "_7" ::
  "_8" ::
  []

(* maximum bound for counted repetition *)
let counted_quantifiers_bound = 10

(* maximum string length *)
let max_string_length = 100

(* maximum regex AST depth *)
let max_regex_depth = 20

(* maximum run time for a single test, in seconds *)
let timeout = 5

type script
external new_scipt: string -> script = "Script" [@@mel.new] [@@mel.module "node:vm"]
external run_in_context : script -> _ Js.t -> _ Js.t -> 'a = "runInContext" [@@mel.send]
external create_context : _ Js.t -> unit = "createContext" [@@mel.module "node:vm"]

let run_with_timeout (type a) (f: unit -> a) (timeout_sec: int): a option = 
  let run = [%mel.obj { run = f } ] in
  create_context run;
  try Some (run_in_context (new_scipt "run ()") run [%mel.obj { timeout = timeout_sec * 1000 } ]) with _ -> None


let frontend_func_to_string (f: frontend_function) : string =
  match f with
  | Exec -> "exec"
  | Search -> "search"
  | Test -> "test"
  | Match -> "match"
  | MatchAll -> "matchAll"


module Fuzzer (P: EngineParameters) (S: Warblre_js.Encoding.StringLike with type t := P.string) = struct
  open Warblre_js
  open Warblre_js.Extracted.Patterns

  module Engine = Engine(P)
  module Printer = Printer(P)(S)
  let result_to_string: P.string Extracted.ExecArrayExotic.coq_type option -> string =
    Printer.Internal.option_to_string ~none:"No match" (Printer.array_exotic_to_string ~pretty:false)

  (* The JS engine we will be comparing to. *)
  module JsEngine = struct
    module H = Warblre_js.HostEngine.HostEngine(P)(S)
    open H

    let exec (regex: (P.character, P.string, P.property) coq_Regex) (flags: Extracted.RegExpFlags.coq_type) (at: int) (str: P.string): string =
      let r = initialize regex flags in
      setLastIndex r at;
      result_to_string (exec r str)

    let search (regex: (P.character, P.string, P.property) coq_Regex) (flags: Extracted.RegExpFlags.coq_type) (at: int) (str: P.string): string =
      let r = initialize regex flags in
      setLastIndex r at;
      string_of_int (search r str)

    let test (regex: (P.character, P.string, P.property) coq_Regex) (flags: Extracted.RegExpFlags.coq_type) (at: int) (str: P.string): string =
      let r = initialize regex flags in
      setLastIndex r at;
      string_of_bool (test r str)

    let rmatch (regex: (P.character, P.string, P.property) coq_Regex) (flags: Extracted.RegExpFlags.coq_type) (at: int) (str: P.string): string =
      let r = initialize regex flags in
      setLastIndex r at;
      match rmatch r str with
      | Left (Some r) -> String.concat "\n" (List.map S.to_string r)
      | Left None -> "No match"
      | Right r -> result_to_string r

    let matchAll (regex: (P.character, P.string, P.property) coq_Regex) (flags: Extracted.RegExpFlags.coq_type) (at: int) (str: P.string): string =
      let r = initialize regex flags in
      setLastIndex r at;
      String.concat "\n---\n" (List.map (fun e -> result_to_string (Option.some e)) (matchAll r str))

    let run (regex: (P.character, P.string, P.property) coq_Regex) (flags: Extracted.RegExpFlags.coq_type) (at: int) (str: P.string) (f: frontend_function): string =
      match f with
      | Exec -> exec regex flags at str
      | Search -> search regex flags at str
      | Test -> test regex flags at str
      | Match -> rmatch regex flags at str
      | MatchAll -> matchAll regex flags at str
  end
  

  (* Engine extracted from our mechanization. *)
  module RefEngine = struct

    let make_exec_output_stateless (res: (P.character, P.string, P.property) Extracted.execResult): (P.string) Extracted.ExecArrayExotic.coq_type option =
      match res with
      | Null _ -> None
      | Exotic (a, _) -> Some a

    let make_match_output_stateless (res: (P.character, P.string, P.property) Extracted.protoMatchResult): (P.string list option, P.string Extracted.ExecArrayExotic.coq_type option) Either.t =
      match res with
      | GlobalResult (r, _) -> Either.left r
      | NonGlobalResult r -> Either.right (make_exec_output_stateless r)

    let exec (regex: (P.character, P.string, P.property) coq_Regex) (flags: Extracted.RegExpFlags.coq_type) (at: int) (str: P.string): string =
      let r0 = Engine.initialize regex flags in
      let r1 = Engine.setLastIndex r0 (BigInt.of_int at) in
      result_to_string (make_exec_output_stateless (Engine.exec r1 str))

    let search (regex: (P.character, P.string, P.property) coq_Regex) (flags: Extracted.RegExpFlags.coq_type) (at: int) (str: P.string): string =
      let r0 = Engine.initialize regex flags in
      let r1 = Engine.setLastIndex r0 (BigInt.of_int at) in
      BigInt.to_string (fst (Engine.search r1 str))

    let test (regex: (P.character, P.string, P.property) coq_Regex) (flags: Extracted.RegExpFlags.coq_type) (at: int) (str: P.string): string =
      let r0 = Engine.initialize regex flags in
      let r1 = Engine.setLastIndex r0 (BigInt.of_int at) in
      string_of_bool (fst (Engine.test r1 str))

    let rmatch (regex: (P.character, P.string, P.property) coq_Regex) (flags: Extracted.RegExpFlags.coq_type) (at: int) (str: P.string): string =
      let r0 = Engine.initialize regex flags in
      let r1 = Engine.setLastIndex r0 (BigInt.of_int at) in
      match make_match_output_stateless (Engine.rmatch r1 str) with
      | Left (Some r) -> String.concat "\n" (List.map S.to_string r)
      | Left None -> "No match"
      | Right r -> result_to_string r

    let matchAll (regex: (P.character, P.string, P.property) coq_Regex) (flags: Extracted.RegExpFlags.coq_type) (at: int) (str: P.string): string =
      let r0 = Engine.initialize regex flags in
      let r1 = Engine.setLastIndex r0 (BigInt.of_int at) in
      String.concat "\n---\n" (List.map (fun e -> result_to_string (Option.some e)) (fst (Engine.stringMatchAll r1 str)))

    let run (regex: (P.character, P.string, P.property) coq_Regex) (flags: Extracted.RegExpFlags.coq_type) (at: int) (str: P.string) (f: frontend_function): string =
      match f with
      | Exec -> exec regex flags at str
      | Search -> search regex flags at str
      | Test -> test regex flags at str
      | Match -> rmatch regex flags at str
      | MatchAll -> matchAll regex flags at str
  end



  type comparison_result = | Same | Different | Timeout

  (** Comparing 2 engine results *)
  let compare_engines (regex: (Engine.character, Engine.string, P.property) coq_Regex) (flags: Extracted.RegExpFlags.coq_type) (index: int) (str: string) (f: frontend_function): comparison_result =
    let sep = String.init 100 (fun _ -> '-') in
    let input = S.of_string str in
    Printf.printf "\027[36mJS Regex:\027[0m %s\n" (Printer.regex_to_string regex);
    Printf.printf "\027[36mString:\027[0m \"%s\"\n%!" str;
    Printf.printf "\027[36mLastIndex:\027[0m \"%s\"\n%!" (string_of_int index);
    Printf.printf "\027[36mFlags:\027[0m \"%s\"\n%!" (Printer.flags_to_string flags);
    Printf.printf "\027[36mFunction:\027[0m \"%s\"\n%!" (frontend_func_to_string f);

    Printf.printf "\027[34m%s\027[0m\n%!" sep;
    Printf.printf "\027[35mIrregexp (node) result:\027[0m\n%!";
    let node_result = run_with_timeout (fun _ -> JsEngine.run regex flags index input f) timeout in
    Printf.printf "\027[34m%s\027[0m\n%!" sep;
    Printf.printf "%s\n%!" (Option.value node_result ~default:"Timeout");

    Printf.printf "\027[34m%s\027[0m\n%!" sep;
    Printf.printf "\027[35mWarblre result:\027[0m\n%!";
    let ref_result = run_with_timeout (fun _ -> RefEngine.run regex flags index input f) timeout in
    Printf.printf "\027[34m%s\027[0m\n%!" sep;
    Printf.printf "%s\n%!" (Option.value ref_result ~default:"Timeout");

    (* The outputs are compared in string format
        This is the easy solution since, depending on the frontend function, the output type can differ.
        A better (but more complicated) approach would be to compare the generated
        JavaScript objects.
    *)
    match node_result, ref_result with
    | Some node_result, Some ref_result ->
      if String.compare (node_result) (ref_result) != 0 then Different else Same
    | _, _ -> Timeout

  (** * Generating random regexes *)

  module RegexGenerator = struct
    let random_char () : char =
      let idx = Random.int (List.length alphabet) in
      List.nth alphabet idx

    let random_qp () : coq_QuantifierPrefix =
      match (Random.int 6) with
      | 0 -> Star
      | 1 -> Plus
      | 2 -> Question
      | 3 -> let rep = Random.int counted_quantifiers_bound in
            RepExact(BigInt.of_int rep)
      | 4 -> let rep = Random.int counted_quantifiers_bound in
            RepPartialRange(BigInt.of_int rep)
      | 5 -> let minrep = Random.int counted_quantifiers_bound in
            let maxrep = minrep + Random.int counted_quantifiers_bound in
            RepRange(BigInt.of_int minrep, BigInt.of_int maxrep)
      | _ -> failwith "random range error"

    let random_quant () : coq_Quantifier =
      let qp = random_qp () in
      if (Random.bool ()) then Greedy qp else Lazy qp

    let random_char_ranges () : (Engine.character, P.property) coq_ClassRanges =
      let sc c = SourceCharacter (P.Character.from_numeric_value (BigInt.of_int (Char.code c))) in
      List.fold_left (fun current _: (Engine.character, P.property) coq_ClassRanges ->
        if Random.bool() then
          let c = random_char() in
          ClassAtomCR (sc c, current)
        else
          let c1 = random_char() in
          let c2 = random_char() in
          let cs = if c1 <= c2 then (c1, c2) else (c2, c1) in
          RangeCR (sc (fst cs), sc (snd cs), current)
      ) EmptyCR (List.init (Random.int 3) (fun x -> x))

    let randome_group_name (): P.string = 
      let i = Random.int (List.length group_names) in
      S.of_string (List.nth group_names i)

    (* We generate regexes in two steps:
          1.  Random AST are generated, using a ticket system (more tickets = more chances of being generated), 
              where backreferences are all set to 0 (an invalid backref index)
          2.  Backreferences are replaced by indices between 1 and the maximum group index (selected at random).
              If the regex contains no group, backreferences are replaced by the empty regex.
    *)

    (* Table used to generate regex without children (i.e. leafs of the AST) *)
    let ticketTableNonRec: (int * (unit -> (Engine.character, Engine.string, P.property) coq_Regex)) list = [
      ( 1, fun _ -> Empty);
      ( 1, fun _: (Engine.character, Engine.string, P.property) coq_Regex ->
          let r = random_char_ranges () in
          let cc: (Engine.character, P.property) coq_CharClass = if Random.bool() then NoninvertedCC (r) else InvertedCC(r) in
          CharacterClass (cc)
      ); 
      ( 3, fun _ -> let c = random_char() in Char (P.Character.from_numeric_value (BigInt.of_int (Char.code c))));
      ( 1, fun _ -> AtomEsc (DecimalEsc BigInt.zero));
      ( 1, fun _ -> AtomEsc (GroupEsc (S.of_string "")));
      ( 1, fun _ -> Dot);
    ]

    let ticketTableRec: (int * (int -> (int -> (Engine.character, Engine.string, P.property) coq_Regex) -> (Engine.character, Engine.string, P.property) coq_Regex)) list = [
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
            Group (None, r1)
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

    let rec random_ast (depth:int) : (Engine.character, Engine.string, P.property) coq_Regex =
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

    (*  Replace each backreference number with a legal one, between 1 and the maximum group id.
        Replace each backreference name with a legal one.
        Assign the names to the groups.
    *)
    module M = Map.Make(Int)
    let fill_backref_and_groups_names (r: (Engine.character, Engine.string, P.property) coq_Regex) (group_count: int) (names_map: Engine.string M.t) : (Engine.character, Engine.string, P.property) coq_Regex =
      let group_id = ref 0 in
      let names = List.map snd (List.of_seq (M.to_seq names_map)) in
      let rec iter (r: (Engine.character, Engine.string, P.property) coq_Regex)  =
        match r with
        | Empty | Char _ | Dot| CharacterClass _ -> r
        | AtomEsc (GroupEsc _) ->
          if (List.length names = 0) then Empty
          else
            let groupid = Random.int (List.length names) in
            AtomEsc (GroupEsc (List.nth names groupid))
        | AtomEsc (DecimalEsc _) ->
            if (group_count = 0) then Empty
            else
              let groupid = (Random.int group_count) + 1 in
              AtomEsc (DecimalEsc (BigInt.of_int groupid))
        | AtomEsc _ -> r
        | Disjunction (r1,r2) -> Disjunction (iter r1, iter r2)
        | Quantified (r1,quant) -> Quantified (iter r1, quant)
        | Seq (r1,r2) -> Seq (iter r1, iter r2)
        | Group (name, r1) ->
            assert(name = None);
            let name = M.find_opt (!group_id) names_map in
            group_id := (!group_id) + 1;
            Group (name, iter r1)
        | InputStart | InputEnd | WordBoundary | NotWordBoundary -> r
        | Lookahead (r1) -> Lookahead (iter r1)
        | NegativeLookahead (r1) -> NegativeLookahead (iter r1)
        | Lookbehind (r1) -> Lookbehind (iter r1)
        | NegativeLookbehind (r1) -> NegativeLookbehind (iter r1)
      in
      let res = iter r in 
      assert(group_count = (!group_id));
      res

    let generate_group_names_map (group_count: int) (map_size: int): Engine.string M.t =
      assert (map_size <= group_count);
      assert (map_size <= List.length group_names);
      let names = ref (List.map S.of_string group_names) in
      let result: Engine.string M.t ref = ref M.empty in
      let count = ref 0 in
      while !count < map_size do
        let i = Random.int group_count in
        if not (M.mem i (!result)) then
          (let name = List.hd (!names) in
          names := List.tl (!names);
          result := M.add i name (!result);
          count := (!count) + 1)
      done;
      !result
  end

  (* Generate an AST then fills the backreferences numbers *)
  let random_regex (): (Engine.character, Engine.string, P.property) coq_Regex =
    let ast = RegexGenerator.random_ast (Random.int max_regex_depth) in
    let group_count = BigInt.to_int (Engine.countGroups ast) in
    let named_group_count = (Random.int ((min (List.length group_names) group_count) + 1)) in
    let named_groups_map = RegexGenerator.generate_group_names_map group_count named_group_count in
    RegexGenerator.fill_backref_and_groups_names ast group_count named_groups_map

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

  (* MatchAll only works if the g flag is present. *)
  let random_frontend (g: bool) : frontend_function =
    match (Random.int(if g then 5 else 4)) with
    | 0 -> Exec
    | 1 -> Search
    | 2 -> Test
    | 3 -> Match
    | 4 -> MatchAll
    | _ -> failwith "random range error"

  (** * Creating Random Strings  *)
  let random_string () : string =
    let size = (Random.int max_string_length) in
    String.init size (fun _ -> RegexGenerator.random_char ())


  (** * Differential Fuzzer  *)
  let fuzzer ?(start_from=0) (max_tests: int): int =
    let make_sep i = (String.init i (fun _ -> '=')) in
    let iter_witdth = 8 in
    let timeouts = ref 0 in

    let sep = make_sep ((100 - iter_witdth - 2) / 2) in
    for i = 0 to max_tests do
      let rgx = random_regex () in
      let flags = random_flags () in
      let lastindex = Random.int(max_string_length) in
      let str = random_string () in
      let f = random_frontend (Extracted.RegExpFlags.g flags) in
      if (i >= start_from) then (
        Printf.printf "\027[34m%s %*d %s\027[0m\n" sep iter_witdth i sep;
        match compare_engines rgx flags lastindex str f with
        | Same -> ()
        | Different -> (
            Printf.printf "\027[31mEngines disagree!\027[0m\n";
            exit 1
          )
        | Timeout -> timeouts := !timeouts + 1; ()
      )
    done;
    Printf.printf "\027[34m%s\027[0m\n" (make_sep 100);
    !timeouts
end

module F = Fuzzer(Warblre_js.JsEngineParameters.JsParameters)(Warblre_js.JsEngineParameters.JsStringLike)
open F
let () =
  let start_from = 0 in
  let test_count: int = 1000 in
  let user_seed: int option = Some 13 in
  let seed: int = (Option.value (Option.map (fun v _ -> v) user_seed) ~default:(fun _ -> Random.int (1073741823))) () in
  Printf.printf "\027[34mSeed is %d. Starting at test %d.\027[0m\n" seed start_from;
  Random.init seed;
  let timeouts = fuzzer ~start_from:start_from test_count in
  Printf.printf "\027[34mFinished %d tests (%d timeouts).\n" test_count timeouts;