From Warblre Require Import Base Patterns Semantics ClutterFree Frontend ECMA.

From Coq Require Extraction.
Extraction Language OCaml.

From Coq Require extraction.ExtrOcamlBasic.
From Coq Require extraction.ExtrOcamlString.
From Coq Require extraction.ExtrOcamlNatInt.
From Coq Require extraction.ExtrOcamlZInt.

Extract Constant HexDigit.type => "char".
Extract Constant HexDigit.to_integer => "Interop.parse_hex".

Extract Constant AsciiLetter.type => "char".
Extract Constant AsciiLetter.numeric_value => "Char.code".

Extract Constant UInt16.all => "Interop.all_chars".
Extract Constant UInt16.line_terminators => "Interop.line_terminators".
Extract Constant UInt16.white_spaces => "Interop.white_spaces".
Extract Constant UInt16.digits => "Interop.digits".
Extract Constant UInt16.ascii_word_characters => "Interop.ascii_word_characters".

Extract Constant Patterns.GroupName => "string".
Extract Constant Patterns.GroupName_eq_dec => "String.equal".

Extract Constant UInt16.code_points_to_string => "Interop.code_points_to_string".
Extract Constant UInt16.to_upper_case => "Interop.to_upper_case".
Extract Constant UInt16.type => "Interop.character".
Extract Constant UInt16.to_code_point => "Interop.code_point".
Extract Constant UInt16.CodePoint => "Interop.codepoint".
Extract Constant UInt16.numeric_value => "Interop.char_to_int".
Extract Constant UInt16.from_numeric_value => "Interop.char_of_int".
Extract Constant UInt16.compare => "Interop.cmp".

Extraction "Extracted.ml" RegExp.RegExp  ECMA.ECMA.

