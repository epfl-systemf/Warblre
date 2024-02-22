open Yojson
open Warblre.Interop
open Warblre.Extracted.Patterns

let find_field ls name = let (_, r) = List.find (fun (n, _) -> String.equal n name) ls in r

let reduce_left f ls = match ls with
  | h :: t -> List.fold_left f h t
  | _ -> failwith "Cannot reduce empty list"

let json_to_regex (json: (string * Yojson.Safe.t) list) index: Warblre.Extracted.Frontend.coq_RegExpInstance =
  Yojson.Safe.(
    let iter_ca (json: Yojson.Safe.t): coq_ClassAtom = (match json with
    | `Assoc (("type", `String "Char") :: ("value", `String _) :: ("kind", `String "simple") :: ("symbol", `String _) :: ("codePoint", `Int codepoint) :: ("escaped", `Bool true) :: []) ->
       ClassEsc (ClassEscape.CharacterEsc (CharacterEscape.IdentityEsc (Warblre.Interop.char_of_int codepoint)))
    | `Assoc (("type", `String "Char") :: ("value", `String _) :: ("kind", `String "simple") :: ("symbol", `String _) :: ("codePoint", `Int codepoint) :: []) ->
      SourceCharacter (Warblre.Interop.char_of_int codepoint)
    | `Assoc (("type", `String "Char") :: ("value", `String _) :: ("kind", `String "unicode") :: ("symbol", `String _) :: ("codePoint", `Int codepoint) :: []) ->
      SourceCharacter (Warblre.Interop.char_of_int codepoint)

    | `Assoc (("type", `String "Char") :: ("value", `String "\\b") :: ("kind", `String "meta") :: ("symbol", `String ".") :: ("codePoint", `Null) :: []) ->
      ClassEsc(ClassEscape.Coq_b)
    | `Assoc (("type", `String "Char") :: ("value", `String "\\s") :: ("kind", `String "meta") :: ("codePoint", `Null) :: []) ->
      ClassEsc (ClassEscape.CharacterClassEsc (CharacterClassEscape.Coq_s))
    | `Assoc (("type", `String "Char") :: ("value", `String "\\d") :: ("kind", `String "meta") :: ("codePoint", `Null) :: []) ->
      ClassEsc (ClassEscape.CharacterClassEsc (CharacterClassEscape.Coq_d))
    | `Assoc (("type", `String "Char") :: ("value", `String "\\w") :: ("kind", `String "meta") :: ("codePoint", `Null) :: []) ->
      ClassEsc (ClassEscape.CharacterClassEsc (CharacterClassEscape.Coq_w))
    | `Assoc (("type", `String "Char") :: ("value", `String "\\S") :: ("kind", `String "meta") :: ("codePoint", `Null) :: []) ->
      ClassEsc (ClassEscape.CharacterClassEsc (CharacterClassEscape.S))
    | `Assoc (("type", `String "Char") :: ("value", `String "\\D") :: ("kind", `String "meta") :: ("codePoint", `Null) :: []) ->
      ClassEsc (ClassEscape.CharacterClassEsc (CharacterClassEscape.D))
    | `Assoc (("type", `String "Char") :: ("value", `String "\\W") :: ("kind", `String "meta") :: ("codePoint", `Null) :: []) ->
      ClassEsc (ClassEscape.CharacterClassEsc (CharacterClassEscape.W))

    | `Assoc (("type", `String "Char") :: ("value", `String "\\t") :: ("kind", `String "meta") :: ("symbol", `String _) :: ("codePoint", `Int _) :: []) ->
      ClassEsc (ClassEscape.CharacterEsc (CharacterEscape.ControlEsc (ControlEscape.Coq_t)))
    | `Assoc (("type", `String "Char") :: ("value", `String "\\n") :: ("kind", `String "meta") :: ("symbol", `String _) :: ("codePoint", `Int _) :: []) ->
      ClassEsc (ClassEscape.CharacterEsc (CharacterEscape.ControlEsc (ControlEscape.Coq_n)))
    | `Assoc (("type", `String "Char") :: ("value", `String "\\f") :: ("kind", `String "meta") :: ("symbol", `String _) :: ("codePoint", `Int _) :: []) ->
      ClassEsc (ClassEscape.CharacterEsc (CharacterEscape.ControlEsc (ControlEscape.Coq_f)))
    | `Assoc (("type", `String "Char") :: ("value", `String "\\v") :: ("kind", `String "meta") :: ("symbol", `String _) :: ("codePoint", `Int _) :: []) ->
      ClassEsc (ClassEscape.CharacterEsc (CharacterEscape.ControlEsc (ControlEscape.Coq_v)))
    | `Assoc (("type", `String "Char") :: ("value", `String "\\r") :: ("kind", `String "meta") :: ("symbol", `String _) :: ("codePoint", `Int _) :: []) ->
      ClassEsc (ClassEscape.CharacterEsc (CharacterEscape.ControlEsc (ControlEscape.Coq_r)))

    | `Assoc (("type", `String "Char") :: ("value", `String ctrl) :: ("kind", `String "control") :: []) ->
      assert(String.length ctrl == 3);
      ClassEsc (ClassEscape.CharacterEsc (CharacterEscape.AsciiControlEsc (String.get ctrl 2)))
    | `Assoc (("type", `String "Char") :: ("value", `String hex) :: ("kind", `String "hex") :: ("symbol", `String _) :: ("codePoint", `Int _) :: []) ->
      assert(String.length hex == 4);
      ClassEsc (ClassEscape.CharacterEsc (CharacterEscape.HexEscape (String.get hex 2, String.get hex 3)))

    | _  -> failwith (String.cat "Unsupported JSON class atom: " (Yojson.Safe.show json)))
    in


    let rec iter_cc (json: Yojson.Safe.t list): coq_ClassRanges = (match json with
    | `Assoc (("type", `String "Char") :: r) :: t -> ClassAtomCR (iter_ca (`Assoc (("type", `String "Char") :: r)), iter_cc t)

    | `Assoc (("type", `String "ClassRange") :: ("from", from) :: ("to", until) :: []) :: t->
      RangeCR (iter_ca from, iter_ca until, iter_cc t)

    | h :: _ -> failwith (String.cat "Unsupported JSON class ranges: " (Yojson.Safe.show h))
    | [] -> EmptyCR)
    in


    let iter_quantifier (json: Yojson.Safe.t): coq_Quantifier = (match json with
    | `Assoc (("type", `String "Quantifier") :: ("kind", `String "?") :: ("greedy", `Bool true) :: []) -> Greedy (Question)
    | `Assoc (("type", `String "Quantifier") :: ("kind", `String "*") :: ("greedy", `Bool true) :: []) -> Greedy (Star)
    | `Assoc (("type", `String "Quantifier") :: ("kind", `String "+") :: ("greedy", `Bool true) :: []) -> Greedy (Plus)
    | `Assoc (("type", `String "Quantifier") :: ("kind", `String "Range") :: ("from", `Int from) :: ("greedy", `Bool true) :: []) -> Greedy (RepPartialRange (from))
    | `Assoc (("type", `String "Quantifier") :: ("kind", `String "Range") :: ("from", `Int from) :: ("to", `Int until) :: ("greedy", `Bool true) :: []) -> Greedy (RepRange (from, until))

    | `Assoc (("type", `String "Quantifier") :: ("kind", `String "?") :: ("greedy", `Bool false) :: []) -> Lazy (Question)
    | `Assoc (("type", `String "Quantifier") :: ("kind", `String "*") :: ("greedy", `Bool false) :: []) -> Lazy (Star)
    | `Assoc (("type", `String "Quantifier") :: ("kind", `String "+") :: ("greedy", `Bool false) :: []) -> Lazy (Plus)
    | `Assoc (("type", `String "Quantifier") :: ("kind", `String "Range") :: ("from", `Int from) :: ("greedy", `Bool false) :: []) -> Lazy (RepPartialRange (from))
    | `Assoc (("type", `String "Quantifier") :: ("kind", `String "Range") :: ("from", `Int from) :: ("to", `Int until) :: ("greedy", `Bool false) :: []) -> Lazy (RepRange (from, until))

    | _ -> failwith (String.cat "Unsupported JSON class ranges: " (Yojson.Safe.show json)))
    in


    let rec iter_r (json: Yojson.Safe.t): coq_Regex = (match json with
    | `Null -> Empty

    | `Assoc (("type", `String "Char") :: ("value", `String _) :: ("kind", `String "simple") :: ("symbol", `String _) :: ("codePoint", `Int codepoint) :: ("escaped", `Bool true) :: []) ->
        AtomEsc (AtomEscape.CharacterEsc (CharacterEscape.IdentityEsc (Warblre.Interop.char_of_int codepoint)))
    | `Assoc (("type", `String "Char") :: ("value", `String _) :: ("kind", `String "simple") :: ("symbol", `String _) :: ("codePoint", `Int codepoint) :: []) -> Char (Warblre.Interop.char_of_int codepoint)
    | `Assoc (("type", `String "Char") :: ("value", `String _) :: ("kind", `String "unicode") :: ("symbol", `String _) :: ("codePoint", `Int codepoint) :: []) -> Char (Warblre.Interop.char_of_int codepoint)

    | `Assoc (("type", `String "Char") :: ("value", `String "\\0") :: ("kind", `String "zero") :: []) -> AtomEsc (AtomEscape.CharacterEsc CharacterEscape.Zero)
    | `Assoc (("type", `String "Char") :: ("value", `String ".") :: ("kind", `String "meta") :: ("symbol", `String ".") :: ("codePoint", `Null) :: []) ->
      Dot

    | `Assoc (("type", `String "Char") :: ("value", `String "\\t") :: ("kind", `String "meta") :: ("symbol", `String _) :: ("codePoint", `Int _) :: []) ->
      AtomEsc (AtomEscape.CharacterEsc (CharacterEscape.ControlEsc (ControlEscape.Coq_t)))
    | `Assoc (("type", `String "Char") :: ("value", `String "\\n") :: ("kind", `String "meta") :: ("symbol", `String _) :: ("codePoint", `Int _) :: []) ->
      AtomEsc (AtomEscape.CharacterEsc (CharacterEscape.ControlEsc (ControlEscape.Coq_n)))
    | `Assoc (("type", `String "Char") :: ("value", `String "\\f") :: ("kind", `String "meta") :: ("symbol", `String _) :: ("codePoint", `Int _) :: []) ->
      AtomEsc (AtomEscape.CharacterEsc (CharacterEscape.ControlEsc (ControlEscape.Coq_f)))
    | `Assoc (("type", `String "Char") :: ("value", `String "\\v") :: ("kind", `String "meta") :: ("symbol", `String _) :: ("codePoint", `Int _) :: []) ->
      AtomEsc (AtomEscape.CharacterEsc (CharacterEscape.ControlEsc (ControlEscape.Coq_v)))
    | `Assoc (("type", `String "Char") :: ("value", `String "\\r") :: ("kind", `String "meta") :: ("symbol", `String _) :: ("codePoint", `Int _) :: []) ->
      AtomEsc (AtomEscape.CharacterEsc (CharacterEscape.ControlEsc (ControlEscape.Coq_r)))

    | `Assoc (("type", `String "Char") :: ("value", `String ctrl) :: ("kind", `String "control") :: []) ->
      assert(String.length ctrl == 3);
      AtomEsc (AtomEscape.CharacterEsc (CharacterEscape.AsciiControlEsc (String.get ctrl 2)))
    | `Assoc (("type", `String "Char") :: ("value", `String hex) :: ("kind", `String "hex") :: ("symbol", `String _) :: ("codePoint", `Int _) :: []) ->
      assert(String.length hex == 4);
      AtomEsc (AtomEscape.CharacterEsc (CharacterEscape.HexEscape (String.get hex 2, String.get hex 3)))

    | `Assoc (("type", `String "Char") :: ("value", `String "\\s") :: ("kind", `String "meta") :: ("codePoint", `Null) :: []) ->
      AtomEsc (AtomEscape.CharacterClassEsc (CharacterClassEscape.Coq_s))
    | `Assoc (("type", `String "Char") :: ("value", `String "\\d") :: ("kind", `String "meta") :: ("codePoint", `Null) :: []) ->
      AtomEsc (AtomEscape.CharacterClassEsc (CharacterClassEscape.Coq_d))
    | `Assoc (("type", `String "Char") :: ("value", `String "\\w") :: ("kind", `String "meta") :: ("codePoint", `Null) :: []) ->
      AtomEsc (AtomEscape.CharacterClassEsc (CharacterClassEscape.Coq_w))
    | `Assoc (("type", `String "Char") :: ("value", `String "\\S") :: ("kind", `String "meta") :: ("codePoint", `Null) :: []) ->
      AtomEsc (AtomEscape.CharacterClassEsc (CharacterClassEscape.S))
    | `Assoc (("type", `String "Char") :: ("value", `String "\\D") :: ("kind", `String "meta") :: ("codePoint", `Null) :: []) ->
      AtomEsc (AtomEscape.CharacterClassEsc (CharacterClassEscape.D))
    | `Assoc (("type", `String "Char") :: ("value", `String "\\W") :: ("kind", `String "meta") :: ("codePoint", `Null) :: []) ->
      AtomEsc (AtomEscape.CharacterClassEsc (CharacterClassEscape.W))

    | `Assoc (("type", `String "CharacterClass") :: ("expressions", `List expressions) :: []) -> CharacterClass (NoninvertedCC (iter_cc expressions))
    | `Assoc (("type", `String "CharacterClass") :: ("negative", `Bool true) :: ("expressions", `List expressions) :: []) ->
      CharacterClass (InvertedCC (iter_cc expressions))

    | `Assoc (("type", `String "Disjunction") :: ("left", left) :: ("right", right) :: _) -> Disjunction (iter_r left, iter_r right)
    | `Assoc (("type", `String "Alternative") :: ("expressions", `List expressions) :: _) -> expressions |> List.map iter_r |> reduce_left (fun l r -> Seq (l, r))

    | `Assoc (("type", `String "Repetition") :: ("expression", expression) :: ("quantifier", quantifier) :: []) -> Quantified (iter_r expression, iter_quantifier quantifier)

    | `Assoc (("type", `String "Group") :: ("capturing", `Bool false) :: ("expression", expression)  :: []) ->
      iter_r expression
    | `Assoc (("type", `String "Group") :: ("capturing", `Bool true) :: ("number", `Int _) :: ("expression", expression)  :: []) ->
      Group (None, iter_r expression)
    | `Assoc (("type", `String "Group") :: ("capturing", `Bool true) :: ("name", `String name) :: ("nameRaw", `String _) :: ("number", `Int _) :: ("expression", expression)  :: []) ->
      Group (Some name, iter_r expression)

    | `Assoc (("type", `String "Backreference") :: ("kind", `String "number") :: ("number", `Int i) :: ("reference", `Int _)  :: []) ->
      AtomEsc (AtomEscape.DecimalEsc i)
    | `Assoc (("type", `String "Backreference") :: ("kind", `String "name") :: ("reference", `String name) :: ("referenceRaw", `String _)  :: []) ->
      AtomEsc (AtomEscape.GroupEsc name)

    | `Assoc (("type", `String "Assertion") :: ("kind", `String "^") :: []) -> InputStart
    | `Assoc (("type", `String "Assertion") :: ("kind", `String "$") :: []) -> InputEnd
    | `Assoc (("type", `String "Assertion") :: ("kind", `String "\\b") :: []) -> WordBoundary
    | `Assoc (("type", `String "Assertion") :: ("kind", `String "\\B") :: []) -> NotWordBoundary

    | `Assoc (("type", `String "Assertion") :: ("kind", `String "Lookahead") :: ("assertion", assertion) :: []) -> Lookahead (iter_r assertion)
    | `Assoc (("type", `String "Assertion") :: ("kind", `String "Lookahead") :: ("negative", `Bool true) :: ("assertion", assertion) :: []) -> NegativeLookahead (iter_r assertion)
    | `Assoc (("type", `String "Assertion") :: ("kind", `String "Lookbehind") :: ("assertion", assertion) :: []) -> Lookbehind (iter_r assertion)
    | `Assoc (("type", `String "Assertion") :: ("kind", `String "Lookbehind") :: ("negative", `Bool true) :: ("assertion", assertion) :: []) -> NegativeLookbehind (iter_r assertion)

    | _ -> failwith (String.cat "Unsupported JSON regex: " (Yojson.Safe.show json)))
    in


    let string_to_flags str =
      Warblre.Extracted.Frontend.(
        {
          d = String.contains str 'd';
          g = String.contains str 'g';
          i = String.contains str 'i';
          m = String.contains str 'm';
          s = String.contains str 's';
          u = String.contains str 'u';
          v = String.contains str 'v';
          y = String.contains str 'y';
        })
    in
    match find_field json "body", find_field json "flags" with
    | ast, `String flags ->
        let ast = iter_r ast in
        let flags = string_to_flags flags in
        if flags.u then failwith "'u' is not yet supported"
        else
          (match (Warblre.Extracted.Frontend.coq_RegExpInitialize ast flags) with
          | Success x -> Warblre.Extracted.Frontend.setlastindex x index
          | Failure _ -> failwith "Compile error")
    | _ -> failwith "Invalid JSON regex")