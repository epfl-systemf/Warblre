open Warblre_js.Engines
open Warblre_js.Printers

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

module Fuzzer (P: EngineParameters) (S: Warblre_js.Encoding.StringLike with type t := P.string) = struct
  open Warblre_js
  open Warblre_js.Extracted.Patterns

  (* The JS engine we will be comparing to. *)
  module JsEngine = struct
    module H = Warblre_js.HostEngine.HostEngine(P)(S)
    open H

    let exec (regex: (P.character, P.string, P.property) coq_Regex) (flags: Extracted.RegExpFlags.coq_type) (at: int) (str: P.string):
    (P.string) Extracted.ExecArrayExotic.coq_type option =
      let r = initialize regex flags in
      setLastIndex r at;
      exec r str
  end
  
  module E = Engine(P)
  open E
  module Pr = Printer(P)(S)
  open Pr

  (* Engine extracted from our mechanization. *)
  module RefEngine = struct

    let make_output_stateless (res: (P.character, P.string, P.property) Extracted.execResult): (P.string) Extracted.ExecArrayExotic.coq_type option =
      match res with
      | Null _ -> None
      | Exotic (a, _) -> Some a

    let exec (regex: (P.character, P.string, P.property) coq_Regex) (flags: Extracted.RegExpFlags.coq_type) (at: int) (str: P.string): (P.string) Extracted.ExecArrayExotic.coq_type option =
      let r0 = initialize regex flags in
      let r1 = setLastIndex r0 (BigInt.of_int at) in
      make_output_stateless (exec r1 str)
  end



  type comparison_result = | Same | Different

  (** * Comparing 2 engine results *)
  (* TODO: Ideally, the engines should be run with a timeout in case the runtime explodes.
      A setup as in https://github.com/janestreet/async/blob/master/example/timeouts.ml might allow to do just that.
      TODO: maybe JS allows to do this more easily.
  *)
  let compare_engines (regex: (character, string, P.property) coq_Regex) (flags: Extracted.RegExpFlags.coq_type) (index: int) (str: ocaml_string) (_: frontend_function): comparison_result =
    let result_to_string = Internal.option_to_string ~none:"No match" (array_exotic_to_string ~pretty:false) in
    let sep = String.init 100 (fun _ -> '-') in
    Printf.printf "\027[36mJS Regex:\027[0m %s\n" (regex_to_string regex);
    Printf.printf "\027[36mString:\027[0m \"%s\"\n%!" str;
    Printf.printf "\027[36mLastIndex:\027[0m \"%s\"\n%!" (string_of_int index);
    Printf.printf "\027[36mFlags:\027[0m \"%s\"\n%!" (flags_to_string flags);
    (* Printf.printf "\027[36mFunction:\027[0m \"%s\"\n%!" (frontend_func f); *)
    Printf.printf "\027[91m%s\027[0m\n" sep;
    Printf.printf "\027[35mIrregexp (node) result:\027[0m\n%!";
    let input = S.of_string str in
    let node_result = JsEngine.exec regex flags index input in
    Printf.printf "%s\n" (result_to_string node_result);
    Printf.printf "\027[91m%s\027[0m\n" sep;
    Printf.printf "\027[35mWarblre result:\027[0m\n%!";
    let ref_result = RefEngine.exec regex flags index input in
    Printf.printf "%s\n" (result_to_string ref_result);
    (* The outputs are compared in string format;
        A better (but more complicated) approach would be to compare the generated
        JavaScript objects.
    *)
    if String.compare (result_to_string node_result) (result_to_string ref_result) != 0 then Different else Same

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

    let random_char_ranges () : (character, P.property) coq_ClassRanges =
      let sc c = SourceCharacter (P.Character.from_numeric_value (Host.of_int (Char.code c))) in
      List.fold_left (fun current _: (character, P.property) coq_ClassRanges ->
        if Random.bool() then
          let c = random_char() in
          ClassAtomCR (sc c, current)
        else
          let c1 = random_char() in
          let c2 = random_char() in
          let cs = if c1 <= c2 then (c1, c2) else (c2, c1) in
          RangeCR (sc (fst cs), sc (snd cs), current)
      ) EmptyCR (List.init (Random.int 3) (fun x -> x))

    let randome_group_name (): string = 
      let i = Random.int (List.length group_names) in
      S.of_string (List.nth group_names i)

    (* We generate regexes in two steps:
          1.  Random AST are generated, using a ticket system (more tickets = more chances of being generated), 
              where backreferences are all set to 0 (an invalid backref index)
          2.  Backreferences are replaced by indices between 1 and the maximum group index (selected at random).
              If the regex contains no group, backreferences are replaced by the empty regex.
    *)

    (* Table used to generate regex without children (i.e. leafs of the AST) *)
    let ticketTableNonRec: (int * (unit -> (character, string, P.property) coq_Regex)) list = [
      ( 1, fun _ -> Empty);
      ( 1, fun _: (character, string, P.property) coq_Regex ->
          let r = random_char_ranges () in
          let cc: (character, P.property) coq_CharClass = if Random.bool() then NoninvertedCC (r) else InvertedCC(r) in
          CharacterClass (cc)
      ); 
      ( 3, fun _ -> let c = random_char() in Char (P.Character.from_numeric_value (BigInt.of_int (Char.code c))));
      ( 1, fun _ -> AtomEsc (DecimalEsc BigInt.zero));
      ( 1, fun _ -> AtomEsc (GroupEsc (S.of_string "")));
      ( 1, fun _ -> Dot);
    ]

    let ticketTableRec: (int * (int -> (int -> (character, string, P.property) coq_Regex) -> (character, string, P.property) coq_Regex)) list = [
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

    let rec random_ast (depth:int) : (character, string, P.property) coq_Regex =
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
    let fill_backref_and_groups_names (r: (character, string, P.property) coq_Regex) (group_count: int) (names_map: string M.t) : (character, string, P.property) coq_Regex =
      let group_id = ref 0 in
      let names = List.map snd (List.of_seq (M.to_seq names_map)) in
      let rec iter (r: (character, string, P.property) coq_Regex)  =
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

    let generate_group_names_map (group_count: int) (map_size: int): string M.t =
      assert (map_size <= group_count);
      assert (map_size <= List.length group_names);
      let names = ref (List.map S.of_string group_names) in
      let result: string M.t ref = ref M.empty in
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
  let random_regex (): (character, string, P.property) coq_Regex =
    let ast = RegexGenerator.random_ast (Random.int max_regex_depth) in
    let group_count = BigInt.to_int (countGroups ast) in
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

  (* does not generate matchall if there is no global flag *)
  let random_frontend (_: bool) : frontend_function =
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
    String.init size (fun _ -> RegexGenerator.random_char ())


  (** * Differential Fuzzer  *)
  let fuzzer ?(start_from=0) (max_tests: int) : unit =
    let make_sep i = (String.init i (fun _ -> '=')) in
    let iter_witdth = 8 in
    
    let sep = make_sep ((100 - iter_witdth - 2) / 2) in
    for i = 0 to max_tests do
      let rgx = random_regex () in
      let flags = random_flags () in
      let lastindex = Random.int(max_string_length) in
      let str = random_string () in
      let f = random_frontend (flags.g) in
      if (i >= start_from) then (
        Printf.printf "\027[91m%s %*d %s\027[0m\n" sep iter_witdth i sep;
        if (compare_engines rgx flags lastindex str f = Different) then (
          failwith "Engines disagree!"
        )
      )
    done;
    Printf.printf "\027[91m%s\027[0m\n" (make_sep 100)


end

module F = Fuzzer(Warblre_js.JsEngineParameters.JsParameters)(Warblre_js.JsEngineParameters.JsStringLike)
open F
let () =
  let start_from = 0 in
  let test_count: int = 100 in
  let user_seed: int option = None in
  let seed: int = (Option.value (Option.map (fun v _ -> v) user_seed) ~default:(fun _ -> Random.int (1073741823))) () in
  Printf.printf "\027[91mSeed is %d. Starting at test %d.\027[0m\n" seed start_from;
  Random.init seed;
  fuzzer ~start_from:start_from test_count;
  Printf.printf "\027[91mFinished %d tests.\027[0m\n" test_count;