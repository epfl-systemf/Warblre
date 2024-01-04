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
  let test_str = "dddbaababaaaabc" in
  let list_input = List.init (String.length test_str) (String.get test_str) in

  let test_flags:Extracted.Frontend.coq_RegExpFlags =
    { d=false;
      g=true;
      i=false;
      m=false;
      s=false;
      u=false;
      v=false;
      y=false;
    } in

  let maxgroup = Extracted.StaticSemantics.countLeftCapturingParensWithin test_rgx [] in
  let matcher = Extracted.Semantics.compilePattern test_rgx maxgroup in

  
  let test_instance :Extracted.Frontend.coq_RegExpInstance =
    { coq_OriginalFlags = test_flags;
      coq_RegExpRecord = maxgroup; (* todo: missing some flags *)
      coq_RegExpMatcher = matcher;
      lastIndex = 0;
      pattern = test_rgx;
    } in

  let test_result = Extracted.Frontend.coq_PrototypeTest test_instance list_input in
  let _ = match test_result with
    | Success (true, newinstance) -> Printf.printf "true\n"
    | Success (false, newinstance) -> Printf.printf "false\n"
    | _ -> failwith "Failure\n"
  in

  let search_result = Extracted.Frontend.coq_PrototypeSearch test_instance list_input in
  let _ = match search_result with
    | Success (i, newinstance) -> Printf.printf "Search index: %d\n" i
    | _ -> failwith "Failure\n"
  in
  ()


  
  
  
  (* fuzzer () *)
