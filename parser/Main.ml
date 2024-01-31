open! Parser
open! Lexer
open Warblre
open Extracted.Patterns
open Extracted.Notation
open Extracted.Result


(** * Debugging the parser: printing the parsed AST *)
let print_charclassescape (c:CharacterClassEscape.coq_type) : string =
  match c with
  | Coq_d -> "Coq_d"
  | D -> "D"
  | Coq_s -> "Coq_s"
  | S -> "S"
  | Coq_w -> "Coq_w"
  | W -> "W"

let print_controlescape (c:ControlEscape.coq_type) : string =
  match c with
  | Coq_f -> "Coq_f"
  | Coq_n -> "Coq_n"
  | Coq_r -> "Coq_r"
  | Coq_t -> "Coq_t"
  | Coq_v -> "Coq_v"

let print_charescape (c:CharacterEscape.coq_type) : string =
  match c with
  | ControlEsc (e) -> "ControlEsc(" ^ print_controlescape e ^ ")"
  | Zero -> "Zero"
  | IdentityEsc (e) -> "IdentityEsc(\'" ^ String.make 1 e ^ "\')"

let print_atomescape (a:AtomEscape.coq_type) : string =
  match a with
  | DecimalEsc (i) -> "DecimalEsc(" ^ string_of_int i ^ ")"
  | CharacterClassEsc (c) -> "CharacterClassEsc(" ^ print_charclassescape c ^ ")"
  | CharacterEsc (c) -> "CharacterEsc(" ^ print_charescape c ^ ")"
  | GroupEsc (gn) -> "GroupEsc(\"" ^ gn ^ "\")"

let print_quantprefix (q:coq_QuantifierPrefix) : string =
  match q with
  | Star -> "Star"
  | Plus -> "Plus"
  | Question -> "Question"
  | RepExact (i) -> "RepExact(" ^ string_of_int i ^ ")"
  | RepPartialRange (i) -> "RepPartialRange(" ^ string_of_int i ^ ")"
  | RepRange (i1,i2) -> "RepRange(" ^ string_of_int i1 ^ "," ^ string_of_int i2 ^ ")"

let print_quantifier (q:coq_Quantifier) : string =
  match q with
  | Greedy(q) -> "Greedy(" ^ print_quantprefix q ^ ")"
  | Lazy(q) -> "Lazy(" ^ print_quantprefix q ^ ")"

let print_stringop (so:string option) : string =
  match so with
  | None -> "None"
  | Some s -> "Some(" ^ s ^ ")"

let rec print_regex (r:coq_Regex) : string =
  match r with
  | Empty -> "Empty"
  | Char c -> "Char(\'" ^ String.make 1 c ^ "\')"
  | Dot -> "Dot"
  | AtomEsc a -> "AtomEsc(" ^ print_atomescape a ^ ")"
  | CharacterClass _ -> failwith "todo"
  | Disjunction (r1, r2) -> "Disjunction(" ^ print_regex r1 ^ "," ^ print_regex r2 ^ ")"
  | Quantified (r1, q) -> "Quantified(" ^ print_regex r1 ^ "," ^ print_quantifier q ^ ")"
  | Seq (r1, r2) -> "Seq(" ^ print_regex r1 ^ "," ^ print_regex r2 ^ ")"
  | Group (go, r1) -> "Group(" ^ print_stringop go ^ "," ^ print_regex r1 ^ ")"
  | Lookahead (r1) -> "Lookahead(" ^ print_regex r1 ^ ")"
  | NegativeLookahead (r1) -> "NegativeLookahead(" ^ print_regex r1 ^ ")"
  | Lookbehind (r1) -> "Lookbehind(" ^ print_regex r1 ^ ")"
  | NegativeLookbehind (r1) -> "NegativeLookbehind(" ^ print_regex r1 ^ ")"


(** * Calling the Parser  *)

let parse_regex (str:string) : coq_Regex =
  Parser.main Lexer.token (Lexing.from_string str)

(** * Calling the Reference Implementation *)
(* TODO: adapt to frontend function *)
(* maybe share some printing functions with the fuzzer *)

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
(* TODO: switch to a frontend function *)
let rec get_first_result matcher list_str string_input start: string =
  let maxlength = List.length list_str in
  match (matcher list_str start) with
  | Success (Some result) ->
     print_result result start string_input
  | Success None ->
     if (maxlength = start) then ("NoMatch\n\n") (* reached the end *)
     else get_first_result matcher list_str string_input (start+1)
(* trying to find a match starting at the next string position *)
  | Failure Extracted.MatchError.OutOfFuel -> failwith "Match failure"
  | Failure Extracted.MatchError.AssertionFailed -> failwith "Match failure"

(* calling the reference implementation *)
let get_reference_result (regex:coq_Regex) (str:string) : string =
  let maxgroup = Extracted.StaticSemantics.countLeftCapturingParensWithin regex [] in
  let rer = {
    RegExp.ignoreCase = false;
    RegExp.multiline = false;
    RegExp.dotAll = false;
    RegExp.unicode = false;
    RegExp.capturingGroupsCount = maxgroup;
  } in
  match Extracted.Semantics.compilePattern regex rer with
  | Success matcher ->
    let list_input = List.init (String.length str) (String.get str) in
    get_first_result matcher list_input str 0
  | Failure Extracted.CompileError.AssertionFailed -> failwith "Compile failure"

let _ =
  Printf.printf "\027[36mEnter your regex:\027[0m\n";
  let input_regex = read_line () in
  let regex = parse_regex input_regex in
  let regex_ast = print_regex regex in
  Printf.printf "\027[33mYour parsed regex is:\027[0m\n%s\n" regex_ast;

  Printf.printf "\027[36mEnter your string:\027[0m\n";
  let input_str = read_line () in

  let resultop = get_reference_result regex input_str in
  Printf.printf "\027[33mYour match result is:\027[0m\n%s\n" resultop;
  ()
