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
  
  external parseRegExpLiteral: JsEngineParameters.JsString.t -> regex = "parseRegExpLiteral" [@@mel.module "@eslint-community/regexpp"]
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
      ~onAlternative:(fun _ children -> reduce children (fun acc child -> Seq (acc, child)) (fun _ -> Empty))
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
