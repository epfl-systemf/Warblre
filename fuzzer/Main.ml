open Warblre
open Extracted.Patterns
open Notations
open Helpers


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
(* we restrict ourselves to a small alphabet *)
(* with a dash (non-ascii) to test word boundaries *)
let alphabet : char list = ['a'; 'b'; '-']

let random_char () : char =
  let idx = Random.int (List.length alphabet) in
  List.nth alphabet idx

(* maximum bound for counted repetition *)
let max_counted = 10

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




(* let max_depth = 50 *)

(* let max_string = 100 *)




let str = "aaaaabaac"
let regex = Group (None, !* (
    Disjunction (
      Group (None, char 'a'),
      Group (None, char 'b'))))

let () =
  ignore (random_char());
  ignore (random_quant());
  let js_regex = regex_to_string regex in
  Printf.printf "regex: %s\n" js_regex; 
  test_regex regex str 0;
  Printf.printf "done\n"
