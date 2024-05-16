open Warblre

module JsStringLike: Encoding.StringLike
  with type t = Js.String.t
= struct
  type t = Js.String.t
  let to_string = fun s -> s
  let of_string = fun s -> s
end

module JsCharacter: Engines.Character with type t = Js.String.t = struct
  type t = Js.String.t
  let equal: t -> t -> bool = [%mel.raw {|
    function (l) { return function (r) { return l === r; }; }
  |}]
  let compare: t -> t -> int  = [%mel.raw {|
    function (l) { return function (r) { return r.charCodeAt(0) - l.charCodeAt(0); }; }
  |}]
  let numeric_value:  t -> int= [%mel.raw {|
    function (c) {
      if (c.length !== 1) { throw new RangeError(c); }
      return c.charCodeAt(0);
    }
  |}]
  let from_numeric_value: int -> t = [%mel.raw {|
    function (i) { return String.fromCharCode(i); }
  |}]
  let max_numeric_value = 0xFFFF

  let to_upper_case: t -> t = [%mel.raw {|
    function (ch) {
      const u = ch.toUpperCase();
      if (u.length > 1) {
        return ch;
      }
      else {
        const cu = u.charCodeAt(0);
        if (numeric_value(ch) >= 128 && cu < 128) {
          return ch;
        }
        else {
          return from_numeric_value(cu);
        }
      }
    }
  |}]
  let canonicalize rer ch =
    match rer with
    | { Extracted.RegExpRecord.ignoreCase = false; _ } -> ch
    | _ -> to_upper_case ch
end

module JsString = struct
  type t = Js.String.t
  let equal: t -> t -> bool = [%mel.raw {|
    function (l) { return function (r) { return l === r; }; }
  |}]
  let length (s: t): int = Js.String.length s
  let substring (str: t) (b: int) (e: int): t = Js.String.slice ~start:b ~end_:e str
  let empty_string = {js||js}

  (* Ideally, character = string, but string = 'a list 
      TODO: change mechanization to not use character list, 
      but any type S with typeclass Indexable S character.
  *)
  let list_from_string (s: t) = Array.to_list (Js.String.split ~sep:"" s)
  let list_to_string s = Stdlib.String.concat "" s
end

module JsParameters : Engines.EngineParameters 
  with type character = Js.String.t
  with type string = Js.String.t
= struct
  module Character = JsCharacter
  type character = Character.t

  module String = struct
    include JsString
    let advanceStringIndex _ i = i + 1
    let getStringIndex _ i = i
  end
  type string = String.t

  module CharSet = Engines.CharSet(Character)
  type char_set = CharSet.t

  module CharSets = Engines.CharSets(Character)

  type property = |
  module Property = struct
    let equal _ _ = false
    let code_points _ = failwith "How was the empty type instanciated?"
  end
end

(* module UnicodeParameters : EngineParameters 
  with type character = int
  with type string = Unsigned.UInt16.t list
= struct
  module Character = IntCharacter
  type character = Character.t

  module String = struct
    let list_from_string str = Encoding.Unicode.list_from_string (Encoding.Utf16.list_to_string str)
    let list_to_string str = Encoding.Utf16.list_from_string (Encoding.Unicode.list_to_string str)

    module Ops = Extracted.UnicodeOps(struct
      type coq_Utf16CodeUnit = Unsigned.UInt16.t
      type coq_Utf16String = Unsigned.UInt16.t list
      let length = List.length
      let codeUnitAt = List.nth
      let is_leading_surrogate c = Encoding.UnicodeUtils.is_high_surrogate (Unsigned.UInt16.to_int c)
      let is_trailing_surrogate c = Encoding.UnicodeUtils.is_low_surrogate (Unsigned.UInt16.to_int c)
    end)
    let advanceStringIndex s i = Utils.Result.get (Ops.advanceStringIndex s i)
    let getStringIndex s i = Utils.Result.get (Ops.getStringIndex s i)


    include CamlString
  end
  type string = String.t

  module CharSet = CharSet(Character)
  type char_set = CharSet.t

  module CharSets = CharSets(Character)

  type property = UnicodeProperty.t
  module Property = struct
    let equal = UnicodeProperty.equal
    let code_points up = UnicodeProperty.filter_for up CharSets.all
  end
end
*)
module JsEngine = struct
  module E = Engines.Engine(JsParameters)
  include E

  module Regexpp = struct 
    module AST = struct
      type alternative
      type boundaryAssertion = {
        kind: Js.String.t;
        (* Warning: defined iff kind = "word" *)
        negate: bool;
      }
      type lookaroundAssertion = {
        kind: Js.String.t;
        negate: bool;
      }
      type backreference = {
        ref: Obj.t
      }
      type capturingGroup = {
        name: Js.String.t Js.nullable
      }
      type character = { value: int }
      type characterClass = {
        unicodeSets: bool;
        (* Warning: defined iff unicodeSets = true *)
        negate: bool;
      }
      type characterClassRange = {
        min: character;
        max: character;
      }
      type characterSet = {
        (* any, digit, space, word, property *)
        kind: Js.String.t;
        (* Warning: defined iff kind != "any" *)
        negate: bool;
      }
      type classIntersection
      type classStringDisjunction
      type classSubtraction
      type expressionCharacterClass
      type group
      type pattern
      type quantifier = {
        raw: Js.String.t;
        min: int;
        max: int;
        greedy: bool;
      }
      type regExpLiteral
      type stringAlternative
    end

    type regex
    
    external parseRegExpLiteral: JsString.t -> regex = "parseRegExpLiteral" [@@mel.module "@eslint-community/regexpp"]
    external map:
      regex ->
      onAlternative:((AST.alternative -> 'a Js.Array.t -> 'a)[@mel.uncurry]) ->
      onBoundaryAssertion:((AST.boundaryAssertion -> 'a)[@mel.uncurry]) ->
      onLookaroundAssertion:((AST.lookaroundAssertion ->'a Js.Array.t -> 'a)[@mel.uncurry]) ->
      onBackreference:((AST.backreference -> 'a)[@mel.uncurry]) ->
      onCapturingGroup:((AST.capturingGroup -> 'a Js.Array.t -> 'a)[@mel.uncurry]) ->
      onCharacter:((AST.character -> 'a)[@mel.uncurry]) ->
      onCharacterClass:((AST.characterClass -> ('b Js.Array.t) -> 'a)[@mel.uncurry]) ->
      onCharacterClassRange:((AST.characterClassRange -> 'a -> 'a -> 'a)[@mel.uncurry]) ->
      onCharacterSet:((AST.characterSet -> 'a)[@mel.uncurry]) ->
      onClassIntersection:((AST.classIntersection -> 'a -> 'a -> 'a)[@mel.uncurry]) ->
      onClassStringDisjunction:((AST.classStringDisjunction -> 'a Js.Array.t -> 'a)[@mel.uncurry]) ->
      onClassSubtraction:((AST.classSubtraction -> 'a -> 'a -> 'a)[@mel.uncurry]) ->
      onExpressionCharacterClass:((AST.expressionCharacterClass -> 'a -> 'a)[@mel.uncurry]) ->
      onGroup:((AST.group -> 'a Js.Array.t -> 'a)[@mel.uncurry]) ->
      onPattern:((AST.pattern -> 'a Js.Array.t -> 'a)[@mel.uncurry]) ->
      onQuantifier:((AST.quantifier -> 'a -> 'a)[@mel.uncurry]) ->
      onRegExpLiteral:((AST.regExpLiteral -> 'a -> 'a)[@mel.uncurry]) ->
      onStringAlternative:((AST.stringAlternative -> 'a Js.Array.t -> 'a)[@mel.uncurry]) ->
      onRangeCharacter:((AST.character -> 'b)[@mel.uncurry]) ->
      onRangeCharacterClassRange:((AST.characterClassRange -> 'b)[@mel.uncurry]) ->
      onRangeCharacterSet:((AST.characterSet -> 'b)[@mel.uncurry]) ->
      'a
      = "map" [@@mel.module "./regexpp-map.mjs"]  [@@mel.scope "RegExpMapper"]

    let parseRegex (str: string): (character, string) Warblre.Extracted.Patterns.coq_Regex = Warblre.Patterns.(
      let ast = parseRegExpLiteral str in
      let wat str = (fun _ _ -> failwith ("Unxpected node. Feature: " ^ str)) in
      let unsupported str = failwith ("Features from version > 13.0 are not supported. Feature: " ^ str) in
      let disjunction = (fun _ children -> Js.Array.reduce ~f:(fun acc child -> Smart.disjunction acc child) ~init:null children) in
      let char_to_char (c: AST.character) = JsCharacter.from_numeric_value (c.value) in
      let last_char (str: Js.String.t) (at: int) = Js.String.charAt ~index:((Js.String.length str) - at - 1) str in
      map ast
        ~onAlternative:(fun _ children -> Js.Array.reduce ~f:(fun acc child -> Smart.seq acc child) ~init:epsilon children)
        ~onBoundaryAssertion:(fun a ->
          match a.kind with
          | "start" -> InputStart
          | "end" -> InputEnd
          | "word" -> if a.negate then NotWordBoundary else WordBoundary
          | _ -> failwith ("Invalid boundary assertion. Kind: " ^ a.kind))
        ~onLookaroundAssertion:(fun a r ->
          let r = disjunction () r in
          match a.kind, a.negate with
          | "lookahead", false -> Lookahead r
          | "lookahead", true -> NegativeLookahead r
          | "lookbehind", false -> Lookbehind r
          | "lookbehind", true -> NegativeLookbehind r
          | _, _ -> failwith ("Invalid boundary assertion. Kind: " ^ a.kind ^ "; Negate: " ^ (string_of_bool a.negate)))
        ~onBackreference:(fun b ->
          (* Test whether the backref is named using "ref"'s type *)
          match Js.Types.classify b.ref with
          | JSNumber n -> AtomEsc (DecimalEsc (int_of_float n))
          | JSString n -> AtomEsc (GroupEsc n)
          | _ -> failwith ("Backref's ref did not have the expected type."))
        ~onCapturingGroup:(fun g r ->
          let name = Js.toOption g.name in
          Group (name, disjunction () r))
        ~onCharacter:(fun c -> Char (char_to_char c))
        ~onCharacterClass:(fun c e ->
          if (c.unicodeSets)
          then unsupported "Unicode sets (v flag)"
          else
            let ranges = Js.Array.reduceRight ~f:(fun acc e -> e acc) ~init:EmptyCR e in
            CharacterClass (if c.negate then InvertedCC ranges else NoninvertedCC ranges)
          )
        ~onCharacterClassRange:(wat "Character class range")
        ~onCharacterSet:(fun s ->
          let mk pos neg = AtomEsc (ACharacterClassEsc (if s.negate then neg else pos)) in
          match s.kind with
          | "any" -> Dot
          | "digit" -> mk Coq_esc_d Coq_esc_D
          | "space" -> mk Coq_esc_s Coq_esc_S
          | "word" -> mk Coq_esc_w Coq_esc_W
          | "property" -> failwith "WIP: unicode properties"
          | _ -> failwith ("Unexpected character set. Kind: " ^ s.kind))
        ~onClassIntersection:(fun _ _ -> unsupported "Class intersection")
        ~onClassStringDisjunction:(fun _ _ -> unsupported "Class disjunction")
        ~onClassSubtraction:(fun _ _ -> unsupported "Class disjunction")
        ~onExpressionCharacterClass:(fun _ _ -> unsupported "Class expression")
        ~onGroup:disjunction
        ~onPattern:disjunction
        ~onQuantifier:(fun q r ->
          let min = q.min in
          let max = if (Js.Float.isFinite (Js.Int.toFloat q.max)) then Some q.max else None in
          (* The AST doesn't explicitly remember the kind of the quantifier; we use the raw text to disambiguate *)
          if (((last_char q.raw 0) = "}") || ((last_char q.raw 1) = "}")) then (
            Smart.quantified r min max q.greedy)
          else (
            let quantifierPrefix: coq_QuantifierPrefix = match min, max with
            | 0, None -> Star
            | 1, None -> Plus
            | 0, Some 1 -> Question
            | _, _ -> failwith "Could not find special quantifier from range."
            in
            let quantifier = if q.greedy then Greedy quantifierPrefix else Lazy quantifierPrefix in
            Quantified (r, quantifier)))
        ~onRegExpLiteral:(fun _ r -> r)
        ~onStringAlternative:(fun _ _ -> unsupported "String alternative")
        ~onRangeCharacter:(fun c k -> ClassAtomCR (SourceCharacter (char_to_char c), k))
        ~onRangeCharacterClassRange:(fun r k -> RangeCR (SourceCharacter (char_to_char r.min), SourceCharacter (char_to_char r.max), k))
        ~onRangeCharacterSet:(fun s k ->
          let neg pos neg = if s.negate then neg else pos in
          let esc = match s.kind with
          | "digit" -> neg Coq_esc_d Coq_esc_D
          | "space" -> neg Coq_esc_s Coq_esc_S
          | "word" -> neg Coq_esc_w Coq_esc_W
          | _ -> failwith ("Unexpected character set. Kind: " ^ s.kind)
          in
          ClassAtomCR (ClassEsc (CCharacterClassEsc esc), k)))
  end

  (* open Warblre.Extracted *)
  (* let regexp (pattern: string) (flags: string): ((character, string) RegExpInstance.coq_type, CompileError.coq_type) Result.coq_Result = ; *)
end
(* module UnicodeEngine = Engine(UnicodeParameters) *)