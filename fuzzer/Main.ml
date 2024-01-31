open Warblre
open Extracted.Patterns
open Extracted.StaticSemantics
open Extracted.Result
open Extracted.Notation
open Notations
open Helpers

(* the different frontend functions we can test *)
type frontend_function =
  | Exec
  | Search
  | Test
  | Match
  | MatchAll

(** * Fuzzer parameters  *)

(* we restrict ourselves to a small alphabet *)
(* with a sharp to test word boundaries *)
let alphabet : char list = ['#'; 'a'; 'b']

(* maximum bound for counted repetition *)
let max_counted = 10

(* maximum string length *)
let max_string = 100

(* maximum regex AST depth *)
let max_depth = 50

(* number of tests the fuzzer does *)
let max_tests = 100


(** * JS Regex pretty-printing *)
(* adding a non-capturing group to a string *)
let noncap (s:string) : string =
  "(?:" ^ s ^ ")"

let quantifier_prefix_to_string (qp:coq_QuantifierPrefix) : string =
  match qp with
  | Star -> "*"
  | Plus -> "+"
  | Question -> "?"
  | RepExact (i) -> "{"^ string_of_int i ^"}"
  | RepPartialRange (i) -> "{"^ string_of_int i ^",}"
  | RepRange (imin,imax) -> "{"^ string_of_int imin ^","^ string_of_int imax ^"}"

let quantifier_to_string (q:coq_Quantifier) : string =
  match q with
  | Greedy (qp) -> quantifier_prefix_to_string qp
  | Lazy (qp) -> quantifier_prefix_to_string qp ^ "?"

let rec regex_to_string (r:coq_Regex) : string =
  match r with
  | Empty -> ""
  | Char (c) -> String.make 1 c
  | Dot -> String.make 1 '.'
  | CharacterClass cc ->
    let class_atom_to_string ca = match ca with
      | SourceCharacter '-' -> failwith "Unsupported char '-'"
      | SourceCharacter c -> String.make 1 c
      | ClassEsc _ -> failwith "TODO"
    in
    let rec range_to_string r = match r with
      | EmptyCR -> ""
      | ClassAtomCR (ca, r) -> (class_atom_to_string ca) ^ (range_to_string r)
      | RangeCR (l, h, r) -> (class_atom_to_string l) ^ "-" ^ (class_atom_to_string h) ^ (range_to_string r)
    in
    (match cc with
    | NoninvertedCC r -> "[" ^ (range_to_string r) ^ "]"
    | InvertedCC r -> "[^" ^ (range_to_string r) ^ "]"
    )
  | AtomEsc (AtomEscape.DecimalEsc gid) ->"\\"^ string_of_int gid
  | AtomEsc _ -> failwith "TODO"
  | Disjunction (r1, r2) -> noncap(regex_to_string r1) ^ "|" ^ noncap(regex_to_string r2)
  | Quantified (r1, q) -> noncap(regex_to_string r1) ^ quantifier_to_string q
  | Seq (r1, r2) -> noncap(regex_to_string r1) ^ noncap(regex_to_string r2)
  | Group (_,r1) -> "("^ regex_to_string r1 ^")" (* ignoring the name for now *)
  | Lookahead (r1) -> "(?="^ regex_to_string r1 ^")"
  | NegativeLookahead (r1) -> "(?!"^ regex_to_string r1 ^")"
  | Lookbehind (r1) -> "(?<="^ regex_to_string r1 ^ ")"
  | NegativeLookbehind (r1) -> "(?<!"^ regex_to_string r1 ^")"

let flags_to_string (flags:Extracted.Frontend.coq_RegExpFlags) : string =
  let s = ref "" in
  if (flags.d) then s := "d" ^ !s;
  if (flags.g) then s := "g" ^ !s;
  if (flags.i) then s := "i" ^ !s;
  if (flags.m) then s := "m" ^ !s;
  if (flags.s) then s := "s" ^ !s;
  if (flags.u) then s := "u" ^ !s;
  if (flags.v) then s := "v" ^ !s;
  if (flags.y) then s := "y" ^ !s;
  !s

(** * Calling the Node Matcher (V8 backtracking)  *)

(* sending the type of frontend function to the JS matcher *)
let frontend_func (f:frontend_function) : string =
  match f with
  | Exec -> "exec"
  | Search -> "search"
  | Test -> "test"
  | Match -> "match"
  | MatchAll -> "matchAll"

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

(* getting the Node result as a string, with a timeout in case of exponential complexity *)
(* when the result is None, a Timeout occurred *)
let get_js_result (regex:coq_Regex) (flags:Extracted.Frontend.coq_RegExpFlags) (lastindex:int) (str:string) (f:frontend_function): string option =
  let js_regex = regex_to_string regex in
  let js_regex = "'" ^ js_regex ^ "'" in (* adding quotes to escape special characters *)
  let js_flags = "'" ^ flags_to_string flags ^ "'" in
  let js_index = string_of_int lastindex in
  let js_func = frontend_func f in
  let js_command = "timeout 5s node fuzzer/jsmatcher.js "
                   ^ js_regex ^ " "
                   ^ js_flags ^ " "
                   ^ js_index ^ " "
                   ^ "'"^str^"'" ^ " "
                   ^ js_func in
  Printf.printf "%s\n%!" js_command;
  let result = string_of_command(js_command) in
  if (String.length result = 0) then None else Some result

(** * Calling the Reference Implementation *)

(* printing the result of different frontend functions *)
let print_slice (string_input:string) single_capture : string =
  match single_capture with
  | None -> "Undefined"
  | Some { CaptureRange.startIndex = s; CaptureRange.endIndex = e } ->
     String.sub string_input s (e-s)
       
let print_char_list (l:char list): string =
  List.fold_left (fun acc c -> acc ^ String.make 1 c) "" l

let print_char_list_option (o:char list option) : string =
  match o with
  | None -> "Undefined"
  | Some l ->
     print_char_list l

let rec print_array_indexed (l:char list option list) (index:int) : string =
  match l with
  | [] -> ""
  | o::l' -> "#"^string_of_int index^":"^print_char_list_option o^"\n"^
               print_array_indexed l' (index+1)

let print_array (l:char list option list) : string =
  print_array_indexed l 0

let print_groups_map (g:Extracted.Frontend.groups_map) : string =
  List.fold_left
    (fun acc (gname, op) -> acc ^ "#"^gname^":"^print_char_list_option op^"\n") "" g

let print_groups_map_option (g:Extracted.Frontend.groups_map option) : string =
  match g with
  | None -> "None"
  | Some g -> print_groups_map g

let print_pair_option (p:(int*int) option) : string =
  match p with
  | None -> "Undefined"
  | Some (i1,i2) -> "("^string_of_int i1^","^string_of_int i2^")"

let rec print_index_array_indexed (l:(int*int) option list) (index:int) : string =
  match l with
  | [] -> ""
  | p::l' -> "#"^string_of_int index^":"^print_pair_option p^"\n"^
               print_index_array_indexed l' (index+1)

let print_index_array (o:(int*int) option list option) : string =
  match o with
  | None -> "None"
  | Some l -> print_index_array_indexed l 0

let print_group_option (p:(string * (int * int) option)) : string =
  match snd p with
  | None -> "Undefined"
  | Some (i1,i2) ->
     "#"^(fst p)^"("^string_of_int i1^","^string_of_int i2^")"

let print_indices_group (o:(string * (int * int) option) list option) : string =
  match o with
  | None -> "None"
  | Some l ->
     List.fold_left
       (fun acc p -> acc ^ print_group_option p ^ "\n") "" l

let print_array_exotic (a:Extracted.Frontend.coq_ArrayExotic) : string =
  let s = ref "" in
  s := !s ^ "index:" ^ string_of_int a.index ^ "\n";
  s := !s ^ "array:" ^ print_array a.array ^ "\n";
  s := !s ^ "groups:" ^ print_groups_map_option a.groups ^ "\n";
  s := !s ^ "indices_array:" ^ print_index_array a.indices_array ^ "\n";
  s := !s ^ "indices_groups:" ^ print_indices_group a.indices_groups ^ "\n";
  !s

let print_array_exotic_list l : string =
  List.fold_left (fun acc a -> acc ^ "-" ^ print_array_exotic a ^ "\n") "" l

let print_exec_result (r:Extracted.Frontend.coq_ExecResult) : string =
  match r with
  | Null _ -> "NoMatch\n\n"
  | Exotic (a,_) -> print_array_exotic a ^ "\n"

let print_match_result (r:Extracted.Frontend.coq_ProtoMatchResult) : string =
  match r with
  | GlobalResult (lo,_) ->
     begin match lo with
     | None -> "NoMatch\n\n"
     | Some l ->
        (List.fold_left (fun acc s -> acc ^ "·" ^ print_char_list s ^ "\n") "" l) ^ "\n"
     end
  | NonGlobalResult e -> print_exec_result e

let get_success (r) =
  match r with
  | Success x -> x
  | Failure Extracted.MatchError.OutOfFuel -> failwith "Failure: Out of Fuel"
  | Failure Extracted.MatchError.AssertionFailed -> failwith "Failure: Assertion"

let get_success_compile (r) =
  match r with
  | Success x -> x
  | Failure _ -> failwith "Compile Error"

(* exec *)
let reference_exec (r:Extracted.Frontend.coq_RegExpInstance) (str) : string =
  let res = get_success (Extracted.Frontend.coq_PrototypeExec r str) in
  print_exec_result res
  
(* search *)
let reference_search (r:Extracted.Frontend.coq_RegExpInstance) (str): string =
  let res = get_success (Extracted.Frontend.coq_PrototypeSearch r str) in
  string_of_int (fst res) ^ "\n"

(* test *)
let reference_test (r:Extracted.Frontend.coq_RegExpInstance) (str): string =
  let res = get_success (Extracted.Frontend.coq_PrototypeTest r str) in
  string_of_bool (fst res) ^ "\n"

(* match *)
let reference_match (r:Extracted.Frontend.coq_RegExpInstance) (str): string =
  let res = get_success (Extracted.Frontend.coq_PrototypeMatch r str) in
  print_match_result res 

(* matchAll *)
let reference_matchall (r:Extracted.Frontend.coq_RegExpInstance) (str): string =
  let res = get_success (Extracted.Frontend.coq_PrototypeMatchAll r str) in
  print_array_exotic_list (fst res) ^ "\n"

let get_reference_result (regex:coq_Regex) (flags:Extracted.Frontend.coq_RegExpFlags) (index:int) (str:string) (f:frontend_function) : string option =
  let instance = get_success_compile (Extracted.Frontend.coq_RegExpInitialize regex flags) in
  let instance = Extracted.Frontend.setlastindex instance index in
  let list_input = List.init (String.length str) (String.get str) in
  match f with
  | Exec -> Some (reference_exec instance list_input)
  | Search -> Some (reference_search instance list_input)
  | Test -> Some (reference_test instance list_input)
  | Match -> Some (reference_match instance list_input)
  | MatchAll -> Some (reference_matchall instance list_input)



(** * Comparing 2 engine results *)

let print_op (o:string option) : string =
  match o with | None -> "None" | Some s -> s

let print_result (s:string option) : string =
  match s with
  | None -> "Timeout\n"
  | Some s -> s

(* calling the two engines and failing if they disagree on the result *)
let compare_engines (regex:coq_Regex) (flags:Extracted.Frontend.coq_RegExpFlags) (index:int) (str:string) (f:frontend_function) : unit =
  Printf.printf "\027[36mJS Regex:\027[0m %s\n" (regex_to_string regex);
  Printf.printf "\027[36mString:\027[0m \"%s\"\n%!" str;
  Printf.printf "\027[36mLastIndex:\027[0m \"%s\"\n%!" (string_of_int index);
  Printf.printf "\027[36mFlags:\027[0m \"%s\"\n%!" (flags_to_string flags);
  Printf.printf "\027[36mFunction:\027[0m \"%s\"\n%!" (frontend_func f);
  let node_result = get_js_result regex flags index str f in
  Printf.printf "\027[35mIrregexp  result:\n\027[0m%s\n%!" (print_result node_result);
  let ref_result = get_reference_result regex flags index str f in
  Printf.printf "\027[35mReference result:\n\027[0m%s\n%!" (print_result ref_result);
  match (node_result, ref_result) with
  | Some noderes, Some refres ->
     assert (String.compare noderes refres = 0)
  | _ -> ()


(** * Generating random regexes *)

let random_char () : char =
  let idx = Random.int (List.length alphabet) in
  List.nth alphabet idx

let random_qp () : coq_QuantifierPrefix =
  match (Random.int 6) with
  | 0 -> Star
  | 1 -> Plus
  | 2 -> Question
  | 3 -> let rep = Random.int max_counted in
         RepExact(rep)
  | 4 -> let rep = Random.int max_counted in
         RepPartialRange(rep)
  | 5 -> let minrep = Random.int max_counted in
         let maxrep = minrep + Random.int max_counted in
         RepRange(minrep, maxrep)
  | _ -> failwith "random range error"

let random_quant () : coq_Quantifier =
  let qp = random_qp () in
  if (Random.bool ()) then Greedy qp else Lazy qp

let random_char_ranges () : coq_ClassRanges =
  List.fold_left (fun current _ ->
    if Random.bool() then
      let c = random_char() in
      ClassAtomCR (SourceCharacter c, current)
    else
      let c1 = random_char() in
      let c2 = random_char() in
      let cs = if c1 <= c2 then (c1, c2) else (c2, c1) in
      RangeCR (SourceCharacter (fst cs), SourceCharacter (snd cs), current)
  ) EmptyCR (List.init (Random.int 3) (fun x -> x))

(* We generate regexes in two steps *)
(* First we generate a random AST, where backreferences are all set to 0 (an invalid backref index) *)
(* Then we compute how many groups have been generated *)
(* Next we replace the backreference indices by indices between 1 and the maximum group index *)
(* If no groups are available, we replace backreferences with empty *)

let ticketTableNonRec: (int * (unit -> coq_Regex)) list = [
  ( 1, fun _ -> Empty);
  ( 1, fun _ ->
      let r = random_char_ranges () in
      let cc = if Random.bool() then NoninvertedCC (r) else InvertedCC(r) in
      CharacterClass (cc)
  ); 
  ( 3, fun _ -> let c = random_char() in Char(c));
  ( 1, fun _ -> AtomEsc (AtomEscape.DecimalEsc 0));
  ( 1, fun _ -> Dot);
]

let ticketTableRec: (int * (int -> (int -> coq_Regex) -> coq_Regex)) list = [
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

let rec random_ast (depth:int) : coq_Regex =
  if (depth=0) then
    let rand = Random.int (Lookup.cardinal base_lookup) in
    let gen = Lookup.find rand base_lookup in
    gen ()
  else
    let rand = Random.int (Lookup.cardinal full_lookup) in
    let gen = Lookup.find rand full_lookup in
    gen depth random_ast

let max_group (r:coq_Regex) : int =
  countLeftCapturingParensWithin_impl r

(* replacing each backreference number with a legal one, between 1 and the maximum group id  *)
let rec fill_backref (r:coq_Regex) (maxgroup:int) : coq_Regex =
  match r with
  | Empty | Char _ | Dot| CharacterClass _ -> r
  | AtomEsc (AtomEscape.DecimalEsc _) ->
      if (maxgroup = 0) then Empty
      else let groupid = (Random.int maxgroup) + 1 in
        AtomEsc (AtomEscape.DecimalEsc groupid)
  | AtomEsc _ -> r
  | Disjunction (r1,r2) -> Disjunction (fill_backref r1 maxgroup, fill_backref r2 maxgroup)
  | Quantified (r1,quant) -> Quantified (fill_backref r1 maxgroup, quant)
  | Seq (r1,r2) -> Seq (fill_backref r1 maxgroup, fill_backref r2 maxgroup)
  | Group (nameop, r1) -> Group (nameop, fill_backref r1 maxgroup)
  | Lookahead (r1) -> Lookahead (fill_backref r1 maxgroup)
  | NegativeLookahead (r1) -> NegativeLookahead (fill_backref r1 maxgroup)
  | Lookbehind (r1) -> Lookbehind (fill_backref r1 maxgroup)
  | NegativeLookbehind (r1) -> NegativeLookbehind (fill_backref r1 maxgroup)

(* generates an AST then fills the backreferences numbers *)
let random_regex (): coq_Regex =
  let ast = random_ast (Random.int max_depth) in
  let maxgroup = max_group ast in
  fill_backref ast maxgroup

(* generates random flags *)
let random_flags () : Extracted.Frontend.coq_RegExpFlags =
  { d=Random.bool();
    g=Random.bool();
    i=Random.bool();
    m=Random.bool();
    s=Random.bool();
    u=false;                    (* unsupported for now *)
    v=false;                    (* unsupported for now *)
    y=Random.bool();
  }

(* does not generate matchall if there is no global flag *)
let random_frontend (glob:bool) : frontend_function =
  let max = if glob then 5 else 4 in
  match (Random.int(max)) with
  | 0 -> Exec
  | 1 -> Search
  | 2 -> Test
  | 3 -> Match
  | 4 -> MatchAll
  | _ -> failwith "random range error"

(** * Creating Random Strings  *)

let random_string () : string =
  let size = (Random.int max_string) in
  String.init size (fun _ -> random_char())


(** * Differential Fuzzer  *)

let fuzzer () : unit =
  for _ = 0 to max_tests do
    let rgx = random_regex () in
    let flags = random_flags () in
    let lastindex = Random.int(max_string) in
    let str = random_string () in
    let f = random_frontend (flags.g) in
    compare_engines rgx flags lastindex str f
  done;
  Printf.printf "Finished %d tests.\n" max_tests


let () =
  Random.self_init();
  fuzzer();


  (* let test_rgx = Group(None,BackReference 1) in *)
  (* let test_str = "-baa-ab-a-b--b-" in *)
  (* let test_flags:Extracted.Frontend.coq_RegExpFlags = *)
  (*   { d=true; *)
  (*     g=true; *)
  (*     i=false; *)
  (*     m=false; *)
  (*     s=false; *)
  (*     u=false; *)
  (*     v=false; *)
  (*     y=true; *)
  (*   } in *)
  (* compare_engines test_rgx test_flags 0 test_str Exec *)



  (* let instance = Extracted.Frontend.coq_RegExpInitialize test_rgx test_flags in *)
  (* let list_input = List.init (String.length test_str) (String.get test_str) in *)
  (* ignore (coq_RegExpBuiltinExec instance list_input) *)
