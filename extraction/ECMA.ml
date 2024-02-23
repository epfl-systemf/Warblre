(* open Interop

let utf16_set = Extracted.CharSet.Parametrized.(
  let module S = Set.Make(Unsigned.UInt16) in
  let from_list ls = List.fold_left (fun s c -> S.add c s) S.empty ls in
  let range s e = List.init (e - s) (fun i -> i + s) in
  unparametrize {
    empty = S.empty;
    from_list = from_list;
    union = S.union;
    singleton = S.singleton;
    size = S.cardinal;
    remove_all = S.diff;
    is_empty = S.is_empty;
    contains = (fun s c -> S.mem c s);
    range = (fun l h -> from_list (List.map char_of_int (range (char_to_int l) ((char_to_int h) + 1))));
    unique = (fun _ f s -> if ((S.cardinal s) = 1) then Extracted.Result.Success (S.choose s) else Extracted.Result.assertion_failed f);
    filter = (fun f s -> S.filter s f);
    exist = (fun p s -> S.exists s p);
  })

let utf16_charCode =  Extracted.Character.(
  {
    eq_dec = char_eq;
    from_numeric_value = char_of_int;
    numeric_value = char_to_int;
    canonicalize = Extracted.UInt16.canonicalize;
    set_type = utf16_set;
    all = Interop.all_chars;
    line_terminators = Interop.line_terminators;
    digits = Interop.digits;
    white_spaces = Interop.white_spaces;
    ascii_word_characters = Interop.ascii_word_characters;
  })

let compilePattern = Extracted.Semantics.compilePattern utf16_charCode
let countLeftCapturingParensWithin r = Extracted.countLeftCapturingParensWithin utf16_charCode r []
type matchResult = (character Extracted.Notation.coq_MatchResult) *)