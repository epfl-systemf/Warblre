From Warblre Require Import Base Semantics.

From Coq Require Extraction.
Extraction Language OCaml.

From Coq Require extraction.ExtrOcamlBasic.
From Coq Require extraction.ExtrOcamlString.
From Coq Require extraction.ExtrOcamlNatInt.
From Coq Require extraction.ExtrOcamlZInt.

Extract Constant IdSet.t => "Interop.Ocaml_Set_Int.t".
Extract Constant IdSet.empty => "Interop.Ocaml_Set_Int.empty".
Extract Constant IdSet.add => "Interop.Ocaml_Set_Int.add".
Extract Constant IdSet.union => "Interop.Ocaml_Set_Int.union".
Extract Constant IdSet.fold => "Interop.Ocaml_Set_Int.fold".

Extract Constant Character => "char".
Extract Constant Character.eqb => "Char.equal".

Extraction "Extracted.ml" Semantics.compilePattern.