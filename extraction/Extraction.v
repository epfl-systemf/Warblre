From Warblre Require Import Base Semantics.

From Coq Require Extraction.
Extraction Language OCaml.

From Coq Require extraction.ExtrOcamlBasic.
From Coq Require extraction.ExtrOcamlString.
From Coq Require extraction.ExtrOcamlNatInt.
From Coq Require extraction.ExtrOcamlZInt.

Extract Constant Character => "char".
Extract Constant Character.eqb => "Char.equal".

Extraction "Extracted.ml" Semantics.compilePattern.