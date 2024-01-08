From Warblre Require Import Base Semantics ClutterFree Frontend.

From Coq Require Extraction.
Extraction Language OCaml.

From Coq Require extraction.ExtrOcamlBasic.
From Coq Require extraction.ExtrOcamlString.
From Coq Require extraction.ExtrOcamlNatInt.
From Coq Require extraction.ExtrOcamlZInt.

Extract Constant Character => "char".
Extract Constant Character.eqb => "Char.equal".

Extract Constant GroupName => "int".
Extract Constant GroupName.eqb => "Int.equal".

Extraction "Extracted.ml" Semantics.compilePattern ClutterFree.regex_match
  Frontend.PrototypeExec Frontend.PrototypeSearch Frontend.PrototypeTest Frontend.PrototypeMatch Frontend.StringPrototypeMatchAll
  Frontend.RegExpInitialize Frontend.setlastindex.
