From Warblre Require Import Base Patterns Semantics Frontend Engine.
From Coq Require Import ZArith.

From Coq Require Extraction.
Extraction Language OCaml.
Set Warnings "-extraction-default-directory".
Set Warnings "-extraction-logical-axiom".


From Coq Require extraction.ExtrOcamlBasic.
From Coq Require extraction.ExtrOcamlString.
From Coq Require extraction.ExtrOcamlNatInt.
From Coq Require extraction.ExtrOcamlZInt.
Extract Constant Pos.to_nat => "(fun c -> c)".

Extract Constant host_string => "string".

Extract Constant CodePoint.type => "Encoding.codepoint".
Extract Constant CodePoint.from_numeric_value => "(fun c -> c)".
Extract Constant CodeUnit.type => "Unsigned.UInt16.t".
Extract Constant CodeUnit.is_leading_surrogate => "(fun i -> Encoding.Utf8Utils.is_high_surrogate (Unsigned.UInt16.to_int i))".
Extract Constant CodeUnit.is_trailing_surrogate => "(fun i -> Encoding.Utf8Utils.is_low_surrogate (Unsigned.UInt16.to_int i))".
Extract Constant CodeUnit.numeric_value => "Unsigned.UInt16.to_int".

Extract Constant String.type => "Unsigned.UInt16.t list".
Extract Constant String.eqdec => "(Utils.List.equal Unsigned.UInt16.equal)".
Extract Constant String.length => "Utils.List.length".
Extract Constant String.substring => "(fun str s e -> Utils.List.take (e - s) (Utils.List.drop s str))".
Extract Constant String.codeUnitAt => "(fun str at -> Utils.List.nth str at)".

Extract Constant HexDigit.type => "char".
Extract Constant HexDigit.to_integer => "Interop.Common.parse_hex".

Extract Constant AsciiLetter.type => "char".
Extract Constant AsciiLetter.numeric_value => "Char.code".

Extraction Inline Frontend.RegExpInstance.setLastIndex.

Extraction "Extracted.ml"  Engine.Engine.

