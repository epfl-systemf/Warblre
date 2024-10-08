open Warblre_js

(* Bind some javascript methods/constants. *)
type 'a descriptor = {
  value: 'a;
  writable: bool;
  enumerable: bool;
  configurable: bool;
}
external define_property: 'a -> Js.String.t -> 'b descriptor -> unit = "defineProperty" [@@mel.scope "Object"]
external get_property: 'a -> Js.String.t -> 'b descriptor = "getOwnPropertyDescriptor" [@@mel.scope "Object"]
let set_field (type a b): a -> Js.String.t -> b -> unit = [%mel.raw {|
  function (obj, field, value) { obj[field] = value; }
|}]

external regexp_prototype: Obj.t = "prototype" [@@mel.scope "RegExp"]
external regexp_prototype_exec: Obj.t  = "exec" [@@mel.scope "RegExp", "prototype"]

(* Approximation of ToLength (from the spec). *)
let to_length: int -> int = [%mel.raw {|
  function (index) {
    index = Number(index);
    if (index === undefined) { index = NaN; }
    
    if (index === null || index === false || isNaN(index)) { index = 0; }
    else if (index === false) { index = 1; }
    if (index <= 0) { index = 0; }
    else if (index > Number.MAX_SAFE_INTEGER) { index = Number.MAX_SAFE_INTEGER; }

    index = Math.trunc(index);
    return index;
  }
|}]

(* pproximation of ToString (from the spec). *)
let to_string: Js.String.t -> Js.String.t = [%mel.raw {|
  function (str) {
    let toPrimitive = function(input) {
      let exoticToPrim = input[Symbol.toPrimitive];
      if (exoticToPrim !== undefined) {
        let result = exoticToPrim(input, 'string');
        if (typeof result !== 'object') { return result; }
        else { throw new TypeError('Exotic toPrimitive returned an object.'); }
      }
      else {
        // OrdinaryToPrimitive
        if (typeof input.toString === 'function' && typeof input.toString() !== 'object') { return input.toString(); }
        if (typeof input.valueOf === 'function' && typeof input.valueOf() !== 'object') { return input.valueOf(); }
        throw new TypeError('Could not convert to string.');
      } 
    };

    if (typeof str === 'string') { return str; }
    if (typeof str === 'symbol') { throw new TypeError('Cannot convert symbol to string'); }
    if (str === undefined) { return 'undefined'; }
    if (str === null) { return 'null'; }
    if (str === true) { return 'true'; }
    if (str === false) { return 'false'; }
    if (typeof str === 'number') { return str.toString(); }
    if (typeof str === 'bigint') { return str.toString(); }
    let primValue = toPrimitive(str);
    return primValue.toString();
} 
|}]

module Exec (
  Parameters: Engines.EngineParameters 
    with type character = Js.String.t
    with type string = Js.String.t
) = struct
  module ArrayExotic = ArrayExotic.ArrayExotic(Parameters)(JsEngineParameters.JsStringLike)
  module Engine = Warblre_js.Engines.Engine(Parameters)
  module Parser = Warblre_js.Parser.Parser(Parameters)(JsEngineParameters.JsStringLike)

  (* Caching too many regexes can be detrimental to the memory consumption. *)
  let max_cache_size = 5
  (*
    As it is not possible for us to to compile the regex at creation,
    we have to compile at match time. However, this means
    recompiling it at every match, which is computationally expensive.
    
    To mitigate this issue, we implement a simple cache to avoid
    repeatedly compiling the same regex if it is used multiple times
    in a row.
  *)
  let regex_cache = Belt.MutableMap.String.make ()

  let exec: (Js.Re.t -> string -> Js.Re.result Js.nullable) = 
    (*  Note that all inputs are not as strictly typed as the (melange) API might suggest.
        We hence have to use conversion functions (to_string & to_length), per the spec.    
    *)
    fun this input0 -> (
      let this_str = "/" ^ (Js.Re.source this) ^ "/" ^ (Js.Re.flags this) in

      (* If not cached *)
      if not (Belt.MutableMap.String.has regex_cache this_str) then (
        (* Compile & cache *)
        let re = Parser.parseRegex this_str in
        let flags0 = to_string (Js.Re.flags this) in
        let flags1 = Extracted.({
          RegExpFlags.d = Js.String.includes ~search:"d" flags0;
          RegExpFlags.g = Js.String.includes ~search:"g" flags0;
          RegExpFlags.i = Js.String.includes ~search:"i" flags0;
          RegExpFlags.m = Js.String.includes ~search:"m" flags0;
          RegExpFlags.s = Js.String.includes ~search:"s" flags0;
          RegExpFlags.u = ();
          RegExpFlags.y = Js.String.includes ~search:"y" flags0;
        }) in
        let inst = Engine.initialize re flags1 in
        Belt.MutableMap.String.update regex_cache this_str (fun _ -> Some inst));

      let inst0 = Belt.MutableMap.String.getExn regex_cache this_str in
      (* If the cache contains too many regexes *)
      if (Belt.MutableMap.String.size regex_cache > max_cache_size) then (
        (* Clear the cache, and only keep this regex in it *)
        Belt.MutableMap.String.clear regex_cache;
        Belt.MutableMap.String.update regex_cache this_str (fun _ -> Some inst0)
      );

      (* Convert inputs to the correct type. *)
      let at = to_length (Js.Re.lastIndex this) in
      let input1 = to_string input0 in

      (* Match the regex against the input string. *)
      let inst1 = Engine.setLastIndex inst0 (BigInt.of_int at) in
      let (res, r) = match Engine.exec inst1 input1 with
      | Null r -> (Js.Nullable.null, r)
      | Exotic (a, r) -> 
        (ArrayExotic.MatchResult.js_of_ocaml (Some a), r)
      in

      (* Last index must be mapped back into a UTF16 index *)
      let e = Parameters.String.getStringIndex input1 r.lastIndex in
      if not (get_property this "lastIndex").writable then Js.Exn.raiseTypeError "lastIndex is not writable.";
      if inst1.originalFlags.g || inst1.originalFlags.y then Js.Re.setLastIndex this (BigInt.to_int e);

      res)
end
module RegularExec = Exec(JsEngineParameters.JsParameters)
module UnicodeExec = Exec(JsEngineParameters.JsUnicodeParameters)

(*
  Some quirky behaviors of exec are not implemented in the mechanization of the frontend,
  as they are tied to the untyped nature of JavaScript, whereas we made the choice to strongly
  type things in our mechanization of the frontend.
*)
let exec: (Js.Re.t -> string -> Js.Re.result Js.nullable) [@mel.this] = 
  fun [@mel.this] this input -> (
    (* Check that it is not being called as a constructor. *)
    let as_constructor: bool = [%mel.raw{| new.target |}] in
    if as_constructor then Js.Exn.raiseTypeError("'exec' is not a constructor.");

    (* Hacky way of thecking that there is an internal [[RegExpMatcher]] slot *)
    (* The related test instead mention the requirement that the internal slot [[Class]] === RegExp; this test likely comes from an earlier iteration of the spec  *)
    let is_regexp: bool = [%mel.raw{| Object.getPrototypeOf(this) === RegExp.prototype |}] in
    if not is_regexp then Js.Exn.raiseTypeError("'exec' must be called on a RegExp.");

    (* Call the correct engine, depending on whether unicode mode is enabled. *)
    if (Js.String.includes ~search:"u" (to_string (Js.Re.flags this))) then UnicodeExec.exec this input
    else RegularExec.exec this input
  )

(*
  Override the value of RegExp.prototype.exec 
  The spec mandates that all the other regex functions funnel
  through it, so overriding that function alone should be sufficient.
*)
let set_regex_exec (f: (Js.Re.t -> Js.String.t -> Js.Re.result Js.nullable)[@mel.this]): unit =
  set_field regexp_prototype "exec" f;
  set_field regexp_prototype_exec "prototype" Js.undefined;
  define_property regexp_prototype_exec "name" { value = "exec"; writable = false; enumerable = false; configurable = true }

let () =
  set_regex_exec exec