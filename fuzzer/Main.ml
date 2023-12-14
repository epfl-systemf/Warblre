open Warblre
open Extracted.Patterns
open Extracted.StaticSemantics
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
let max_tests = 1000


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
    test_regex rgx str 0
  done;
  Printf.printf "Finished %d tests.\n" max_tests


let () =
  Random.self_init();
  ignore (regex_to_string Empty);
  fuzzer ()
