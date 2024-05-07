open Warblre

module Conversion (P: Engines.EngineParameters) (S: Encoding.StringLike with type t := P.string) = struct
  module E = Engines.Engine(P)
  open E
  module Pr = Printers.Printer(P)(S)
  open Pr

  (* class type ['a, 'b] js_pair = object
    method first : 'a Js.readonly_prop
    method second : 'b Js.readonly_prop
  end


  class type streamlined_match_result = object
    method index : int Js.readonly_prop
    method input : Js.js_string Js.t Js.readonly_prop
    method groups : Js.js_string Js.t Js.optdef Js.js_array Js.t Js.readonly_prop
    method namedGroups : (Js.js_string Js.t, Js.js_string Js.t Js.optdef) js_pair Js.t Js.js_array Js.t Js.optdef Js.readonly_prop
    method indices : (int, int) js_pair Js.t Js.optdef Js.js_array Js.t Js.optdef Js.readonly_prop
    method namedIndices : (Js.js_string Js.t, (int, int) js_pair Js.t Js.optdef) js_pair Js.t Js.js_array Js.t Js.optdef Js.readonly_prop
  end *)
  type ('a, 'b) pair = {
    first: 'a;
    second: 'b;
  }

  type streamlined_match_result = {
    index: int;
    input: Js.String.t;
    groups: Js.String.t Js.Nullable.t Js.Array.t;
    namedGroups: (Js.String.t, Js.String.t Js.Nullable.t) pair Js.Array.t Js.Nullable.t;
    indices: (int, int) pair Js.Nullable.t Js.Array.t Js.Nullable.t;
    namedIndices: (Js.String.t, (int, int) pair Js.Nullable.t) pair Js.Array.t Js.Nullable.t;
  }

  (* Js function which makes match_result easier to manipulate from OCaml *)
  let streamline_match_result : Js.Re.result Js.Nullable.t -> streamlined_match_result Js.Nullable.t = [%mel.raw {|
    function exec_result_repack (r) {
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

  let streamlined_match_result_to_result (r: streamlined_match_result Js.Nullable.t): (character, string) Extracted.ExecArrayExotic.coq_type option =
    let to_mapped_option (type a b) (f: a -> b) (o: a Js.Nullable.t): b option = Option.map f (Js.Nullable.toOption o) in
    let to_mapped_list (type a b) (f: a -> b) (a: a Js.Array.t): b list = List.map f (Array.to_list a) in
    let to_mapped_tuple (type a b c d) (f: a -> c) (g: b -> d) (p: (a, b) pair): (c * d) = (f p.first, g p.second) in
    let to_tuple = to_mapped_tuple (fun x -> x) (fun x -> x) in
    (* TODO: conversion *)
    let to_string str = (S.of_string str) in
    r |> Js.Nullable.toOption
      |> Option.map (fun (r: streamlined_match_result) ->
        Extracted.ExecArrayExotic.({
          index = r.index;
          input = to_string (r.input);
          array = to_mapped_list (to_mapped_option to_string) (r.groups);
          groups = to_mapped_option (to_mapped_list (to_mapped_tuple to_string (to_mapped_option to_string))) (r.namedGroups); 
          indices_array = to_mapped_option (to_mapped_list (to_mapped_option to_tuple)) (r.indices);
          indices_groups = (to_mapped_option (to_mapped_list (to_mapped_tuple to_string (to_mapped_option to_tuple)))) (r.namedIndices);
        })
      )

  module MatchResult = struct
    let ocaml_of_js (r: Js.Re.result Js.nullable): (character, string) Extracted.ExecArrayExotic.coq_type option =
      r |> streamline_match_result |> streamlined_match_result_to_result
  end
end