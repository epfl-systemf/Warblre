(* Parameters to instantiate the extract engine for Melange *)

(*
  In Melange, the encoding of strings is extremely confusing.
  Javascript assumes that strings will be encoded in UTF16, yet
  OCaml string literal are encoded in UTF8, and the two types (Js.String.t and string)
  are equal.
  
  Since this engine is meant to be called from JavaScript code (mainly test262),
  we assume that strings are correctly encoded in UTF16.
  Hence, this module conversions are identity.
*)
module JsStringLike: Encoding.StringLike
  with type t = Js.String.t
= struct
  type t = Js.String.t
  let to_string = fun s -> s
  let of_string = fun s -> s
end

(* In JavaScript, characters are represented as strings. *)
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

(*
   A character set with a cache for its canonicalized version.

   The specification is written in a way which forces sets to be
   repeatedly canonicalized. The extracted engine's performance
   hence suffers from this.
   This set implementation is made to alleviate this issue.

   Note that canonicalization is affected by the RegExp Record
   passed as argument. Only the last canonicalization is cached;
   requesting another canonicalization will hence evict the currently cached result.
*)
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
  let unique err (s: t): C.t = if S.size s.set = 1 then to_char (Option.get (S.minimum s.set)) else Interop.error err
  let filter (s: t) (p: C.t -> bool): t = mk (S.keep s.set (fun c -> p (to_char c)))
  let exist (s: t) (p: C.t -> bool): bool = S.some s.set (fun i -> p (to_char i))
  let exist_canonicalized (rer) (s: t) c: bool =
    let i = from_char c in
    match s.canonicalized_cache with
    | Some (cached_rer, cached_set) when cached_rer = rer -> S.has cached_set i
    | _ -> (
      let canonicalized = canonicalize rer s.set in
      s.canonicalized_cache <- Some (rer, canonicalized);
      S.has canonicalized i)
end

(* Parameters to instantiate the 'regular' and 'unicode' engines. *)

module JsParameters : Engines.EngineParameters 
  with type character = Js.String.t
  with type string = Js.String.t
  with type property = UnicodeProperties.NoProperty.t
= struct
  module Character = JsUtf16Character
  type character = Character.t

  module String = struct
    include JsString
    (* Ideally, character = string, but string = 'a list 
        LATER: change mechanization to not use character list, 
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

  module Property = UnicodeProperties.NoProperty
  type property = Property.t
end

module JsUnicodeParameters : Engines.EngineParameters 
  with type character = Js.String.t
  with type string = Js.String.t
  with type property = UnicodeProperties.UnicodeProperty.t
= struct
  module Character = JsUnicodeCharacter
  type character = Character.t

  module String = struct
    include JsString
    (* Ideally, character = string, but string = 'a list 
        LATER: change mechanization to not use character list, 
        but any type S with typeclass Indexable S character.
    *)
    let list_from_string (s: t) = Array.to_list (Js.Array.from (Js.String.unsafeToArrayLike s))
    
    module Ops = Extracted.API.Utils.UnicodeOps(struct
      type coq_Utf16CodeUnit = Js.String.t
      type coq_Utf16String = Js.String.t
      let length ls = BigInt.of_int (Js.String.length ls)
      let codeUnitAt _ ls at = Js.String.charAt ~index:(BigInt.to_int at) ls
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

  module Property = struct
    include UnicodeProperties.UnicodeProperty

    (* Adapt a function to work on strings *)
    let char_adapter f = fun c -> f (Option.get (Js.String.codePointAt ~index:0 c))
  
    let code_points up =
      let f = char_adapter (match up with
      | Alphabetic -> Alphabetic.is_alphabetic)
      in
      List.filter f CharSets.all
  end
  type property = Property.t
end
