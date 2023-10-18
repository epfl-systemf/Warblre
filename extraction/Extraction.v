From Warblre Require Import Core.

From Coq Require Extraction.
From Coq Require extraction.ExtrOcamlString.
From Coq Require extraction.ExtrOcamlBasic.

Extraction Language OCaml.
Extract Constant Regex.Character => "char".

Extract Constant Regex.IdentifierName => "int".

Extract Constant Regex.IdSet.t => "Interop.Ocaml_Set_Int.t".
Extract Constant Regex.IdSet.empty => "Interop.Ocaml_Set_Int.empty".
Extract Constant Regex.IdSet.add => "Interop.Ocaml_Set_Int.add".
Extract Constant Regex.IdSet.union => "Interop.Ocaml_Set_Int.union".
Extract Constant Regex.IdSet.fold => "Interop.Ocaml_Set_Int.fold".

Extract Constant Regex.DMap.t "'a" => "'a Interop.Ocaml_Map_Int.t".
Extract Constant Regex.DMap.empty => "Interop.Ocaml_Map_Int.empty".
Extract Constant Regex.DMap.add => "Interop.Ocaml_Map_Int.add".
Extract Constant Regex.DMap.remove => "Interop.Ocaml_Map_Int.remove".
Extraction "Extracted.ml" Regex.Semantics.Semantics.compilePattern.