(*
  The regex functions typically return array (or object) exotic, i.e.
  arrays which have fields (or objects which can be indexed). 
  
  Melange doesn't really provide tools to deal with them, so we provide
  so functions to transform some specific object exotic into more practical
  types ('unexotify'), and reversly ('exotify').
*)
module ArrayExotic (P: Engines.EngineParameters) (S: Encoding.StringLike with type t := P.string) = struct
  type ('a, 'b) pair = {
    first: 'a;
    second: 'b;
  }

  type unexotic_match_result = {
    index: int;
    input: Js.String.t;
    groups: Js.String.t Js.Nullable.t Js.Array.t;
    namedGroups: (Js.String.t, Js.String.t Js.Nullable.t) pair Js.Array.t Js.Nullable.t;
    indices: (int, int) pair Js.Nullable.t Js.Array.t Js.Nullable.t;
    namedIndices: (Js.String.t, (int, int) pair Js.Nullable.t) pair Js.Array.t Js.Nullable.t;
  }

  (* Js function which makes match_result easier to manipulate from OCaml... *)
  let unexotify_match_result : Js.Re.result Js.Nullable.t -> unexotic_match_result Js.Nullable.t = [%mel.raw {|
    function (r) {
      function object_to_array (a) {
        if (a == null || a == undefined) { return a; }
  
        var res = [];
        for (var key in a) {
            res.push({first: key, second: a[key]})
        }
        return res;
      }
  
      function array_to_pair (p) {
        if (p == null || p == undefined) { return p; }
        return { first: p[0], second: p[1] };
      }

      if (r == null || r == undefined) { return null; }

      return {
          index: r.index,
          input: r.input,
          groups: r.slice(),
          namedGroups: object_to_array(r.groups),
          indices: r.indices?.slice()?.map(array_to_pair),
          namedIndices: object_to_array(r.indices?.groups)?.map(p => { return { first: p.first, second: array_to_pair(p.second) } }),
      };
    }
  |}]

  (* ... and its reverse operation. *)
  let exotify_match_result : unexotic_match_result Js.Nullable.t -> Js.Re.result Js.Nullable.t = [%mel.raw {|
    function (r) {
      function array_of_pairs_to_object (a, f = (x) => x) {
        if (a == null || a == undefined) { return a; }
        
        var res = Object.create(null);
        for (var { first: first, second: second } of a) {
          Object.defineProperty(res, first, { value: f(second), enumerable: true, writable: true, configurable: true })
        }
        return res;
      }

      function pair_to_array (p) {
        if (p == null || p == undefined) { return p; }
        return [ p.first, p.second ];
      }

      var result = r.groups.slice();
      Object.defineProperty(result, 'groups', { value: array_of_pairs_to_object(r.namedGroups), enumerable: true, writable: true, configurable: true });
      result.index = r.index;
      if (r.indices !== undefined) {
        Object.defineProperty(result, 'indices', { value: r.indices.slice().map(pair_to_array), enumerable: true, writable: true, configurable: true });
        
        Object.defineProperty(result.indices, 'groups', { value: array_of_pairs_to_object(r.namedIndices?.slice(), pair_to_array), enumerable: true, writable: true, configurable: true });
      }
      result.input = r.input;

      return result;
    }
  |}]

  let unexotic_match_result_to_result (r: unexotic_match_result Js.Nullable.t): (P.string) Extracted.ExecArrayExotic.coq_type option =
    let to_mapped_option (type a b) (f: a -> b) (o: a Js.Nullable.t): b option = Option.map f (Js.Nullable.toOption o) in
    let to_mapped_list (type a b) (f: a -> b) (a: a Js.Array.t): b list = List.map f (Array.to_list a) in
    let to_mapped_tuple (type a b c d) (f: a -> c) (g: b -> d) (p: (a, b) pair): (c * d) = (f p.first, g p.second) in
    let to_tuple = to_mapped_tuple BigInt.of_int BigInt.of_int in
    let to_string str = (S.of_string str) in
    r |> Js.Nullable.toOption
      |> Option.map (fun (r: unexotic_match_result) ->
        Extracted.ExecArrayExotic.({
          index = BigInt.of_int (r.index);
          input = to_string (r.input);
          array = to_mapped_list (to_mapped_option to_string) (r.groups);
          groups = to_mapped_option (to_mapped_list (to_mapped_tuple to_string (to_mapped_option to_string))) (r.namedGroups); 
          indices_array = to_mapped_option (to_mapped_list (to_mapped_option to_tuple)) (r.indices);
          indices_groups = (to_mapped_option (to_mapped_list (to_mapped_tuple to_string (to_mapped_option to_tuple)))) (r.namedIndices);
        })
      )

  let result_to_unexotic_match_result (r: (P.string) Extracted.ExecArrayExotic.coq_type option): unexotic_match_result Js.Nullable.t =
    let nonify_nil (type a) (ls: a list option) = Option.bind ls (fun ls -> if List.is_empty ls then None else Some ls) in
    let to_mapped_nullable (type a b) (f: a -> b) (o: a option): b Js.Nullable.t = Js.Nullable.fromOption (Option.map f o) in
    let to_mapped_array (type a b) (f: a -> b) (a: a list): b Js.Array.t = Array.of_list (List.map f a) in
    let to_mapped_pair (type a b c d) (f: a -> c) (g: b -> d) (p: a * b): (c, d) pair = { first = f (fst p); second = g (snd p)} in
    let to_pair = to_mapped_pair BigInt.to_int BigInt.to_int in
    let to_string str = (S.to_string str) in
    r |> Option.map (fun (r: (P.string) Extracted.ExecArrayExotic.coq_type) ->
        {
          index = BigInt.to_int r.index;
          input = to_string (r.input);
          groups = to_mapped_array (to_mapped_nullable to_string) (r.array);
          namedGroups = to_mapped_nullable (to_mapped_array (to_mapped_pair to_string (to_mapped_nullable to_string))) (nonify_nil r.groups); 
          indices = to_mapped_nullable (to_mapped_array (to_mapped_nullable to_pair)) (nonify_nil r.indices_array);
          namedIndices = (to_mapped_nullable (to_mapped_array (to_mapped_pair to_string (to_mapped_nullable to_pair)))) (nonify_nil r.indices_groups);
        }
      )|> Js.Nullable.fromOption

  module MatchResult = struct
    let ocaml_of_js (r: Js.Re.result Js.nullable): (P.string) Extracted.ExecArrayExotic.coq_type option =
      r |> unexotify_match_result |> unexotic_match_result_to_result
    let js_of_ocaml (r: (P.string) Extracted.ExecArrayExotic.coq_type option): Js.Re.result Js.nullable =
      r |> result_to_unexotic_match_result |> exotify_match_result
  end
end