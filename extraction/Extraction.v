From Warblre Require Import Base Semantics ClutterFree.

From Coq Require Extraction.
Extraction Language OCaml.

From Coq Require extraction.ExtrOcamlBasic.
From Coq Require extraction.ExtrOcamlString.
From Coq Require extraction.ExtrOcamlNatInt.
From Coq Require extraction.ExtrOcamlZInt.

Extract Constant Character => "char".
Extract Constant Character.eqb => "Char.equal".
Extract Constant Character.eqs => "Char.equal".
Extract Constant Character.numeric_value => "Char.code".
Extract Constant Character.from_numeric_value => "Char.chr".

Extract Constant GroupName => "int".
Extract Constant GroupName.eqb => "Int.equal".

Extract Constant CharSet.line_terminators => "Interop.line_terminators".
Extract Constant CharSet.all => "Interop.all_chars".

Extraction "Extracted.ml" Semantics.compilePattern.