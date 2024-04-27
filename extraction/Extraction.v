From Warblre Require Import Base Patterns Semantics Frontend Engine Fragments.
From Coq Require Import ZArith.

From Coq Require Extraction.
Extraction Language OCaml.

From Coq Require extraction.ExtrOcamlBasic.
From Coq Require extraction.ExtrOcamlString.
From Coq Require extraction.ExtrOcamlNatInt.
From Coq Require extraction.ExtrOcamlZInt.
Extract Constant Pos.to_nat => "(fun c -> c)".

Extract Constant host_string => "string".

Extract Constant HexDigit.type => "char".
Extract Constant HexDigit.to_integer => "Interop.Common.parse_hex".

Extract Constant AsciiLetter.type => "char".
Extract Constant AsciiLetter.numeric_value => "Char.code".

Extraction Inline Frontend.RegExpInstance.setLastIndex.

Extraction "Extracted.ml" Engine.Engine UnicodeOps.

