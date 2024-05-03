open Js_of_ocaml
open Warblre

module Conversion (P: Engines.EngineParameters) (S: Encoding.StringLike with type t := P.string) = struct
  open Engines.Engine(P)
  open Printers.Printer(P)(S)

  class type ['a, 'b] js_pair = object
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
  end

  (* Js function which makes match_result easier to manipulate from OCaml *)
  external streamline_match_result : Js.match_result_handle Js.t Js.opt -> streamlined_match_result Js.t Js.opt = "exec_result_repack"

  let streamlined_match_result_to_result (r: streamlined_match_result Js.t Js.opt): (character, string) Extracted.ExecArrayExotic.coq_type option =
    let to_mapped_option (type a b) (f: a -> b) (o: a Js.optdef): b option = Js.Optdef.to_option (Js.Optdef.map o f) in
    let to_mapped_list (type a b) (f: a -> b) (a: a Js.js_array Js.t): b list = List.map f (Array.to_list (Js.to_array a)) in
    let to_mapped_tuple (type a b c d) (f: a -> c) (g: b -> d) (p: (a, b) js_pair Js.t): (c * d) = (f p##.first, g p##.second) in
    let to_tuple = to_mapped_tuple (fun x -> x) (fun x -> x) in
    let to_string str = (S.of_string (Js.to_string str)) in
    r |> Js.Opt.to_option
      |> Option.map (fun r ->
        Extracted.ExecArrayExotic.({
          index = r##.index;
          input = to_string (r##.input);
          array = to_mapped_list (to_mapped_option to_string) (r##.groups);
          groups = to_mapped_option (to_mapped_list (to_mapped_tuple to_string (to_mapped_option to_string))) (r##.namedGroups); 
          indices_array = to_mapped_option (to_mapped_list (to_mapped_option to_tuple)) (r##.indices);
          indices_groups = (to_mapped_option (to_mapped_list (to_mapped_tuple to_string (to_mapped_option to_tuple)))) (r##.namedIndices);
        })
      )

  module MatchResult = struct
    let ocaml_of_js (r: Js.match_result_handle Js.t Js.opt): (character, string) Extracted.ExecArrayExotic.coq_type option =
      r |> streamline_match_result |> streamlined_match_result_to_result
  end
end