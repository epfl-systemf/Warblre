open Warblre
open Extracted.Patterns
open Extracted.StaticSemantics
open Extracted.Result
open Extracted.Notation
open Notations
open Helpers


(** * Fuzzer parameters  *)

(* we restrict ourselves to a small alphabet *)
(* with a dash (non-ascii) to test word boundaries *)
let alphabet : char list = ['a'; 'b'; '-']

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
  | Disjunction (r1, r2) -> noncap(regex_to_string r1) ^ "|" ^ noncap(regex_to_string r2)
  | Quantified (r1, q) -> noncap(regex_to_string r1) ^ quantifier_to_string q
  | Seq (r1, r2) -> noncap(regex_to_string r1) ^ noncap(regex_to_string r2)
  | Group (_,r1) -> "("^ regex_to_string r1 ^")" (* ignoring the name for now *)
  | Lookahead (r1) -> "(?="^ regex_to_string r1 ^")"
  | NegativeLookahead (r1) -> "(?!"^ regex_to_string r1 ^")"
  | Lookbehind (r1) -> "(?<="^ regex_to_string r1 ^ ")"
  | NegativeLookbehind (r1) -> "(?<!"^ regex_to_string r1 ^")"
  | BackReference (gid) -> "\\"^ string_of_int gid

let flags_to_string (flags:Extracted.Frontend.coq_RegExpFlags) : string =
  let s = ref "" in
  if (flags.s) then s := "d" ^ !s;
  if (flags.g) then s := "g" ^ !s;
  if (flags.i) then s := "i" ^ !s;
  if (flags.m) then s := "m" ^ !s;
  if (flags.s) then s := "s" ^ !s;
  if (flags.u) then s := "u" ^ !s;
  if (flags.v) then s := "v" ^ !s;
  if (flags.y) then s := "y" ^ !s;
  !s
  

(** * Calling the Node Matcher (V8 backtracking)  *)

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
let get_js_result (regex:coq_Regex) (str:string) : string option =
  let js_regex = regex_to_string regex in
  let js_regex = "'" ^ js_regex ^ "'" in (* adding quotes to escape special characters *)
  let js_command = "timeout 5s node fuzzer/jsmatcher.js " ^ js_regex ^ " " ^ "'"^str^"'" in
  let result = string_of_command(js_command) in
  if (String.length result = 0) then None else Some result

(** * Calling the Reference Implementation *)

let print_slice (string_input:string) single_capture : string =
  match single_capture with
  | None -> "Undefined"
  | Some { CaptureRange.startIndex = s; CaptureRange.endIndex = e } ->
     String.sub string_input s (e-s)

(* printing the result of a match *)
let print_result result (start:int) (string_input:string) : string =
  let s = ref "" in
  match result with
  | { MatchState.endIndex = i; MatchState.captures = captures; _ } ->
     (* the substring corresponding to group #0 *)
     let zero_slice = String.sub string_input start (i-start) in
     s := !s ^ "#0:" ^ zero_slice ^ "\n" ;
     (* all other capture group slices *)
     for i = 1 to ((List.length captures)) do
       s := !s ^ "#" ^ string_of_int i ^ ":";
       s := !s ^ print_slice string_input (List.nth captures (i-1)) ^ "\n"
     done;
     !s ^ "\n"
       
(* calling the matcher at different starting position until a match is found *)
let rec get_first_result matcher list_str string_input start: string option =
  let maxlength = List.length list_str in
  let open Extracted in
  match (matcher list_str start) with
  | Success (Some result) ->
     Some (print_result result start string_input)
  | Success None ->
     if (maxlength = start) then (Some "NoMatch\n\n") (* reached the end *)
     else get_first_result matcher list_str string_input (start+1)
(* trying to find a match starting at the next string position *)
  | Failure OutOfFuel -> failwith "Failure"
  | Failure AssertionFailed -> failwith "Failure"

(* calling the reference implementation *)
let get_reference_result (regex:coq_Regex) (str:string) : string option =
  let maxgroup = Extracted.StaticSemantics.countLeftCapturingParensWithin regex [] in
  let matcher = Extracted.Semantics.compilePattern regex maxgroup in
  let list_input = List.init (String.length str) (String.get str) in
  get_first_result matcher list_input str 0

(* printing the results of executing the different frontend functions *)

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
    (fun acc (gname, op) -> acc ^ "#"^string_of_int gname^":"^print_char_list_option op^"\n") "" g

let print_groups_map_option (g:Extracted.Frontend.groups_map option) : string =
  match g with
  | None -> "None"
  | Some g -> print_groups_map g

let print_pair_option (p:(int*int) option) : string =
  match p with
  | None -> "Undefined"
  | Some (i1,i2) -> "("^string_of_int i1^","^string_of_int i2^")"

let print_index_array_indexed (l:(int*int) option list) (index:int) : string =
  List.fold_left
    (fun acc pairop -> acc ^ "#"^string_of_int index^":"^print_pair_option pairop^"\n") "" l

let print_index_array (o:(int*int) option list option) : string =
  match o with
  | None -> "None"
  | Some l -> print_index_array_indexed l 0

let print_group_option (p:(Extracted.groupName * (int * int) option)) : string =
  match snd p with
  | None -> "Undefined"
  | Some (i1,i2) ->
     "#"^string_of_int (fst p)^"("^string_of_int i1^","^string_of_int i2^")"

let print_indices_group (o:(Extracted.groupName * (int * int) option) list option) : string =
  match o with
  | None -> "None"
  | Some l ->
     List.fold_left
       (fun acc p -> acc ^ print_group_option p ^ "\n") "" l

let print_array_exotic (a:Extracted.Frontend.coq_ArrayExotic) : string =
  let s = ref "" in
  s := "index:" ^ string_of_int a.index ^ "\n" ^ !s;
  s := "array:" ^ print_array a.array ^ "\n" ^ !s;
  s := "groups:" ^ print_groups_map_option a.groups ^ "\n" ^ !s;
  s := "indices_array:" ^ print_index_array a.indices_array ^ "\n" ^ !s;
  s := "indices_groups:" ^ print_indices_group a.indices_groups ^ "\n" ^ !s;
  !s

let print_array_exotic_list l : string =
  List.fold_left (fun acc a -> acc ^ print_array_exotic a ^ "\n") "" l

let print_exec_result (r:Extracted.Frontend.coq_ExecResult) : string =
  match r with
  | Null _ -> "NoMatch\n\n"
  | Exotic (a,_) -> print_array_exotic a

let print_match_result (r:Extracted.Frontend.coq_ProtoMatchResult) : string =
  match r with
  | GlobalResult (lo,_) ->
     begin match lo with
     | None -> "None"
     | Some l ->
        List.fold_left (fun acc s -> acc ^ print_char_list s ^ "\n") "" l
     end
  | NonGlobalResult e -> print_exec_result e

(* exec *)
let reference_exec (r:Extracted.Frontend.coq_RegExpInstance) (str:string) : string option =
  let list_input = List.init (String.length str) (String.get str) in
  match (Extracted.Frontend.coq_PrototypeExec r list_input) with
  | Success res -> Some (print_exec_result res)
  | Failure _ -> failwith "Failure"

(* search *)
let reference_search (r:Extracted.Frontend.coq_RegExpInstance) (str:string): string option =
  let list_input = List.init (String.length str) (String.get str) in
  match (Extracted.Frontend.coq_PrototypeSearch r list_input) with
  | Success (res,_) -> Some (string_of_int res)
  | Failure _ -> failwith "failure"

(* test *)
let reference_test (r:Extracted.Frontend.coq_RegExpInstance) (str:string): string option =
  let list_input = List.init (String.length str) (String.get str) in
  match (Extracted.Frontend.coq_PrototypeTest r list_input) with
  | Success (res,_) -> Some (string_of_bool res)
  | Failure _ -> failwith "failure"

(* match *)
let reference_match (r:Extracted.Frontend.coq_RegExpInstance) (str:string): string option =
  let list_input = List.init (String.length str) (String.get str) in
  match (Extracted.Frontend.coq_PrototypeMatch r list_input) with
  | Success res -> Some (print_match_result res)
  | Failure OutOfFuel -> failwith "failure out of fuel"
  | Failure AssertionFailed -> failwith "assertion failed"

(* matchAll *)
let reference_matchall (r:Extracted.Frontend.coq_RegExpInstance) (str:string): string option =
  let list_input = List.init (String.length str) (String.get str) in
  match (Extracted.Frontend.coq_PrototypeMatchAll r list_input) with
  | Success (res,_) -> Some (print_array_exotic_list res)
  | Failure _ -> failwith "failure"


let print_op (o:string option) : string =
  match o with | None -> "None" | Some s -> s

(** * Comparing 2 engine results *)

let print_result (s:string option) : string =
  match s with
  | None -> "Timeout\n"
  | Some s -> s

(* calling the two engines and failing if they disagree on the result *)
let compare_engines (regex:coq_Regex) (str:string) : unit =
  Printf.printf "\027[36mJS Regex:\027[0m %s\n " (regex_to_string regex);
  Printf.printf "\027[36mString:\027[0m \"%s\"\n%!" str;
  let node_result = get_js_result regex str in
  Printf.printf "\027[35mIrregexp  result:\n\027[0m%s\n%!" (print_result node_result);
  let ref_result = get_reference_result regex str in
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


(* We generate regexes in two steps *)
(* First we generate a random AST, where backreferences are all set to 0 (an invalid backref index) *)
(* Then we compute how many groups have been generated *)
(* Next we replace the backreference indices by indices between 1 and the maximum group index *)
(* If no groups are available, we replace backreferences with empty *)

let rec random_ast (depth:int) : coq_Regex =
  (* maximum cases *)
  let max = 13 in
  (* if at max depth, generate only terminals *)
  let rand = if (depth=0) then (Random.int 5) else (Random.int max) in
  match rand with
  | 0 -> Empty
  | 1 | 2 | 3 -> let c = random_char() in Char(c)
  | 4 -> BackReference 0        (* group id to be replaced later *)
  | 5 -> let r1 = random_ast (depth-1) in
         let r2 = random_ast (depth-1) in
         Disjunction (r1, r2)
  | 6 | 7 -> let r1 = random_ast (depth-1) in
         let quant = random_quant () in
         Quantified (r1, quant)
  | 8 -> let r1 = random_ast (depth-1) in
         Group (None, r1)       (* TODO: generate named groups *)
  | 9 -> let r1 = random_ast (depth-1) in
         Lookahead (r1)
  | 10 -> let r1 = random_ast (depth-1) in
         NegativeLookahead (r1)
  | 11 -> let r1 = random_ast (depth-1) in
          Lookbehind (r1)
  | 12 -> let r1 = random_ast (depth-1) in
          NegativeLookbehind (r1)
  | _ -> failwith "random range error"

let max_group (r:coq_Regex) : int =
  countLeftCapturingParensWithin_impl r

(* replacing each backreference number with a legal one, between 1 and the maximum group id  *)
let rec fill_backref (r:coq_Regex) (maxgroup:int) : coq_Regex =
  match r with
  | Empty | Char _ -> r
  | Disjunction (r1,r2) -> Disjunction (fill_backref r1 maxgroup, fill_backref r2 maxgroup)
  | Quantified (r1,quant) -> Quantified (fill_backref r1 maxgroup, quant)
  | Seq (r1,r2) -> Seq (fill_backref r1 maxgroup, fill_backref r2 maxgroup)
  | Group (nameop, r1) -> Group (nameop, fill_backref r1 maxgroup)
  | Lookahead (r1) -> Lookahead (fill_backref r1 maxgroup)
  | NegativeLookahead (r1) -> NegativeLookahead (fill_backref r1 maxgroup)
  | Lookbehind (r1) -> Lookbehind (fill_backref r1 maxgroup)
  | NegativeLookbehind (r1) -> NegativeLookbehind (fill_backref r1 maxgroup)
  | BackReference _ ->
     if (maxgroup = 0) then Empty
     else let groupid = (Random.int maxgroup) + 1 in
          BackReference groupid

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

(** * Creating Random Strings  *)

let random_string () : string =
  let size = (Random.int max_string) in
  String.init size (fun _ -> random_char())


(** * Differential Fuzzer  *)

let fuzzer () : unit =
  for _ = 0 to max_tests do
    let rgx = random_regex () in
    let str = random_string () in
    compare_engines rgx str
  done;
  Printf.printf "Finished %d tests.\n" max_tests


let () =
  Random.self_init();
  (* fuzzer(); *)

  (* let original_bug_regex : coq_Regex = *)
  (*   Quantified ( *)
  (*       Group(None, *)
  (*             Quantified( *)
  (*                 Quantified( *)
  (*                     Disjunction( *)
  (*                         Group(None *)
  (*                              ,BackReference 2) *)
  (*                        ,Empty) *)
  (*                    ,Greedy(Plus)) *)
  (*                ,Greedy(RepRange(8,16))) *)
  (*         ) *)
  (*      ,Greedy(RepExact(6))) in *)
  (* let original_bug_string = "-bbabaa" in *)

  
  (* let bug_regex : coq_Regex = *)
  (*   Group(None,Group(None, Seq(Char('a'),Group(None, Char('b'))))) in *)
  
  
  (* let bug_string = "ab" in *)
  (* compare_engines bug_regex bug_string *)
  (* This bug was fixed by fixing the computation of parens before *)


  let test_rgx = Seq(Quantified(Char('a'),Greedy Star),Char('b')) in
  let test_str = "dddbabaabaaab" in

  let test_flags:Extracted.Frontend.coq_RegExpFlags =
    { d=false;
      g=true;
      i=true;
      m=false;
      s=false;
      u=false;
      v=false;
      y=false;
    } in

  let test_instance : Extracted.Frontend.coq_RegExpInstance =
    Extracted.Frontend.coq_RegExpInitialize test_rgx test_flags in 
  
  Printf.printf "Flags: %s\n" (flags_to_string test_flags);
  Printf.printf "Exec: %s\n" (print_op (reference_exec test_instance test_str));
  Printf.printf "Test: %s\n" (print_op (reference_test test_instance test_str));
  Printf.printf "Search: %s\n" (print_op (reference_search test_instance test_str));
  Printf.printf "Match: %s\n" (print_op (reference_match test_instance test_str));
  Printf.printf "MatchAll: %s\n" (print_op (reference_matchall test_instance test_str));
  ()


  
  
  
  (* fuzzer () *)
