module JsStringLike: Encoding.StringLike
  with type t = Js.String.t
= struct
  type t = Js.String.t
  let to_string = fun s -> s
  let of_string = fun s -> s
end

module JsUtf16Character: Engines.Character with type t = Js.String.t = struct
  type t = Js.String.t
  let equal: t -> t -> bool = [%mel.raw {|
    function (l) { return function (r) { return l === r; }; }
  |}]
  let compare: t -> t -> int  = [%mel.raw {|
    function (l) { return function (r) { return r.charCodeAt(0) - l.charCodeAt(0); }; }
  |}]
  let numeric_value:  t -> BigInt.t = [%mel.raw {|
    function (c) {
      if (c.length !== 1) { throw new RangeError(c); }
      return BigInt(c.charCodeAt(0));
    }
  |}]
  let from_numeric_value: BigInt.t -> t = [%mel.raw {|
    function (i) { return String.fromCharCode(Number(i)); }
  |}]
  let max_numeric_value = BigInt.of_int (0xFFFF)

  let to_upper_case: t -> t = [%mel.raw {|
    function (ch) {
      const u = ch.toUpperCase();
      if (u.length > 1) {
        return ch;
      }
      else {
        const cu = u.charCodeAt(0);
        if (numeric_value(ch) >= BigInt(128) && cu < 128) {
          return ch;
        }
        else {
          return from_numeric_value(BigInt(cu));
        }
      }
    }
  |}]
  let canonicalize rer ch =
    match rer with
    | { Extracted.RegExpRecord.ignoreCase = false; _ } -> ch
    | _ -> to_upper_case ch
end

module JsUnicodeCharacter: Engines.Character with type t = Js.String.t = struct
  type t = Js.String.t
  let equal: t -> t -> bool = [%mel.raw {|
    function (l) { return function (r) { return l === r; }; }
  |}]
  let compare: t -> t -> int  = [%mel.raw {|
    function (l) { return function (r) { return r.codePointAt(0) - l.codePointAt(0); }; }
  |}]
  let numeric_value:  t -> BigInt.t = [%mel.raw {|
    function (c) {
      return BigInt(c.codePointAt(0));
    }
  |}]
  let from_numeric_value: BigInt.t -> t = [%mel.raw {|
    function (i) { return String.fromCodePoint(Number(i)); }
  |}]
  let max_numeric_value = BigInt.of_int (0x10FFFF)

  let canonicalize rer (ch: t): t =
    match rer with
    | { Extracted.RegExpRecord.ignoreCase = false; _ } -> ch
    | _ -> from_numeric_value (BigInt.of_int (SimpleFold.simple_fold (BigInt.to_int (numeric_value ch))))
end

module JsString = struct
  type t = Js.String.t
  let equal: t -> t -> bool = [%mel.raw {|
    function (l) { return function (r) { return l === r; }; }
  |}]
  let length (s: t): BigInt.t = BigInt.of_int (Js.String.length s)
  let substring (str: t) (b: BigInt.t) (e: BigInt.t): t = Js.String.slice ~start:(BigInt.to_int b) ~end_:(BigInt.to_int e) str
  let empty_string = {js||js}
  let list_to_string s = Stdlib.String.concat "" s
end

module NoProperty = struct
  type t = |
  let equal (_: t) (_: t) = false
  let code_points (_: t) = failwith "How was the empty type instanciated?"
end

module CachedCharSet (C: Engines.Character) = struct
  module S = Belt.Set.Int

  let from_char (c: C.t): int = BigInt.to_int (C.numeric_value c)
  let to_char (i: int): C.t = C.from_numeric_value (BigInt.of_int i)
  let canonicalize (rer: Extracted.RegExpRecord.coq_type) (s: S.t): S.t = S.reduce s S.empty (fun acc e -> S.add acc (from_char (C.canonicalize rer (to_char e))))
  let map_internal (s: S.t) (f: C.t -> C.t): S.t = S.reduce s S.empty (fun acc e -> S.add acc (from_char (f (to_char e))))

  type t = {
    set: S.t; 
    mutable canonicalized_cache: (Extracted.RegExpRecord.coq_type * S.t) option;
  }
  let mk s = { set = s; canonicalized_cache = None; }

  let empty: t = mk S.empty
  let from_list (ls: C.t list): t = mk (List.fold_left (fun s v -> S.add s (from_char v)) S.empty ls)
  let union (l: t) (r: t): t = mk (S.union l.set r.set)
  let singleton (e: C.t): t = mk (S.add S.empty (from_char e))
  let remove_all (l: t) (r: t): t = mk (S.diff l.set r.set)
  let is_empty (s: t): bool = S.isEmpty s.set
  let contains (s: t) (c: C.t) = S.has s.set (from_char c)
  let range (l: C.t) (h: C.t): t = mk (S.fromSortedArrayUnsafe (Belt.Array.range (from_char l) (from_char h)))
  let size (s: t): BigInt.t = BigInt.of_int (S.size s.set)
  let unique err (s: t): C.t = if S.size s.set = 1 then to_char (Option.get (S.minimum s.set)) else Interop.failure err
  let filter (s: t) (p: C.t -> bool): t = mk (S.keep s.set (fun c -> p (to_char c)))
  let exist_canonicalized (rer) (s: t) c: bool =
    let i = from_char c in
    match s.canonicalized_cache with
    | Some (cached_rer, cached_set) when cached_rer = rer -> S.has cached_set i
    | _ -> (
      let canonicalized = canonicalize rer s.set in
      s.canonicalized_cache <- Some (rer, canonicalized);
      S.has canonicalized i)
end


module JsParameters : Engines.EngineParameters 
  with type character = Js.String.t
  with type string = Js.String.t
  with type property = NoProperty.t
= struct
  module Character = JsUtf16Character
  type character = Character.t

  module String = struct
    include JsString
    (* Ideally, character = string, but string = 'a list 
        TODO: change mechanization to not use character list, 
        but any type S with typeclass Indexable S character.
    *)
    let list_from_string (s: t) = Array.to_list (Js.String.split ~sep:"" s)
    let advanceStringIndex _ i = BigInt.add i BigInt.one
    let getStringIndex _ i = i
  end
  type string = String.t

  module CharSet = CachedCharSet(Character)
  type char_set = CharSet.t

  module CharSets = Engines.CharSets(Character)

  module Property = NoProperty
  type property = Property.t
end

module JsUnicodeParameters : Engines.EngineParameters 
  with type character = Js.String.t
  with type string = Js.String.t
  with type property = NoProperty.t
= struct
  module Character = JsUnicodeCharacter
  type character = Character.t

  module String = struct
    include JsString
    (* Ideally, character = string, but string = 'a list 
        TODO: change mechanization to not use character list, 
        but any type S with typeclass Indexable S character.
    *)
    let list_from_string (s: t) = Array.to_list (Js.Array.from (Js.String.unsafeToArrayLike s))
    
    module Ops = Extracted.API.Utils.UnicodeOps(struct
      type coq_Utf16CodeUnit = Js.String.t
      type coq_Utf16String = Js.String.t
      let length ls = BigInt.of_int (Js.String.length ls)
      let codeUnitAt ls at = Js.String.charAt ~index:(BigInt.to_int at) ls
      let is_leading_surrogate c = Encoding.UnicodeUtils.is_high_surrogate (BigInt.to_int (Character.numeric_value c))
      let is_trailing_surrogate c = Encoding.UnicodeUtils.is_low_surrogate (BigInt.to_int (Character.numeric_value c))
    end)
    let advanceStringIndex s i = Ops.advanceStringIndex s i
    let getStringIndex s i = Ops.getStringIndex s i
  end
  type string = String.t

  module CharSet = CachedCharSet(Character)
  type char_set = CharSet.t

  module CharSets = Engines.CharSets(Character)

  (* TODO: implement *)
  module Property = NoProperty
  type property = Property.t
end


module Parser(P: Engines.EngineParameters)(S: Encoding.StringLike with type t := P.string) = struct
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
      (* Warning: defined iff unicodeSets = false *)
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

  let parseRegex (str: string): (P.character, P.string, P.property) Extracted.Patterns.coq_Regex = Patterns.(
    let ast = parseRegExpLiteral str in
    let wat str = (fun _ _ -> failwith ("Unxpected node. Feature: " ^ str)) in
    let unsupported str = failwith ("Features from version > 13.0 are not supported. Feature: " ^ str) in
    let reduce (a: 'a Js.Array.t) (f: 'a -> 'a -> 'a) (when_empty: unit -> 'a): 'a =
      match Js.Array.shift a with
      | None -> when_empty ()
      | Some h -> Js.Array.reduce ~f:f ~init:h a
    in
    let disjunction = (fun _ children -> reduce children (fun acc child -> Disjunction (acc, child)) (fun _ -> failwith "Empty disjunction")) in
    let char_to_char (c: AST.character) = P.Character.from_numeric_value (BigInt.of_int c.value) in
    let last_char (str: Js.String.t) (at: int) = Js.String.charAt ~index:((Js.String.length str) - at - 1) str in
    map ast
      ~onAlternative:(fun _ children -> reduce children (fun acc child -> Seq (acc, child)) (fun _ -> failwith "Empty sequence"))
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
        | JSNumber n -> AtomEsc (DecimalEsc (BigInt.of_float n))
        | JSString n -> AtomEsc (GroupEsc (S.of_string n))
        | _ -> failwith ("Backref's ref did not have the expected type."))
      ~onCapturingGroup:(fun g r ->
        let name = Option.map S.of_string (Js.toOption g.name) in
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
        let min = BigInt.of_int q.min in
        let max = if (Js.Float.isFinite (Js.Int.toFloat q.max)) then Some (BigInt.of_int q.max) else None in
        (* The AST doesn't explicitly remember the kind of the quantifier; we use the raw text to disambiguate *)
        if (((last_char q.raw 0) = "}") || ((last_char q.raw 1) = "}")) then (
          quantified r min max q.greedy)
        else (
          let quantifierPrefix: coq_QuantifierPrefix = match max with
          | None -> 
            if (BigInt.equal min BigInt.zero) then (Star)
            else if (BigInt.equal min BigInt.one) then (Plus)
            else failwith "Could not find special quantifier from range."
          | Some v when BigInt.equal v BigInt.one -> 
            if (BigInt.equal min BigInt.zero) then (Question)
            else failwith "Could not find special quantifier from range."
          | _ -> failwith "Could not find special quantifier from range."
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
