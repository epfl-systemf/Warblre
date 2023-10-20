From Warblre Require Import Base Semantics.

From Coq Require Extraction.
Extraction Language OCaml.

From Coq Require extraction.ExtrOcamlBasic.
From Coq Require extraction.ExtrOcamlString.
From Coq Require extraction.ExtrOcamlNatInt.
From Coq Require extraction.ExtrOcamlZInt.

Extract Constant IdentifierName => "int".

Extract Constant IdSet.t => "Interop.Ocaml_Set_Int.t".
Extract Constant IdSet.empty => "Interop.Ocaml_Set_Int.empty".
Extract Constant IdSet.add => "Interop.Ocaml_Set_Int.add".
Extract Constant IdSet.union => "Interop.Ocaml_Set_Int.union".
Extract Constant IdSet.fold => "Interop.Ocaml_Set_Int.fold".

Extract Constant DMap.t "'a" => "'a Interop.Ocaml_Map_Int.t".
Extract Constant DMap.empty => "Interop.Ocaml_Map_Int.empty".
Extract Constant DMap.add => "Interop.Ocaml_Map_Int.add".
Extract Constant DMap.remove => "Interop.Ocaml_Map_Int.remove".

Extract Constant Character => "char".

Extraction "Extracted.ml" Semantics.compilePattern.