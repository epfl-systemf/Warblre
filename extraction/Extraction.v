From Warblre Require Import Base Patterns Semantics ClutterFree Frontend ECMA.
From Coq Require Import ZArith.

From Coq Require Extraction.
Extraction Language OCaml.

From Coq Require extraction.ExtrOcamlBasic.
From Coq Require extraction.ExtrOcamlString.
From Coq Require extraction.ExtrOcamlNatInt.
From Coq Require extraction.ExtrOcamlZInt.
Extract Constant Pos.to_nat => "(fun c -> c)".

Extract Constant HexDigit.type => "char".
Extract Constant HexDigit.to_integer => "Interop.Common.parse_hex".

Extract Constant AsciiLetter.type => "char".
Extract Constant AsciiLetter.numeric_value => "Char.code".

Extract Constant Patterns.GroupName => "string".
Extract Constant Patterns.GroupName_eq_dec => "String.equal".

Extract Constant UInt16.code_points_to_string => "Interop.Utf16.code_points_to_string".
Extract Constant UInt16.to_upper_case => "Interop.Utf16.to_upper_case".
Extract Constant UInt16.type => "Encoding.Utf16.character".
Extract Constant UInt16.to_code_point => "Encoding.Utf16.char_to_int".
Extract Constant UInt16.CodePoint => "Encoding.codepoint".
Extract Constant UInt16.numeric_value => "Encoding.Utf16.char_to_int".
Extract Constant UInt16.from_numeric_value => "Encoding.Utf16.char_from_int".
Extract Constant UInt16.compare => "Encoding.Utf16.cmp".

Extract Constant UInt16.all => "Interop.Utf16.all_chars".
Extract Constant UInt16.line_terminators => "Interop.Utf16.line_terminators".
Extract Constant UInt16.white_spaces => "Interop.Utf16.white_spaces".
Extract Constant UInt16.digits => "Interop.Utf16.digits".
Extract Constant UInt16.ascii_word_characters => "Interop.Utf16.ascii_word_characters".


Extract Constant Unicode.type => "Encoding.Unicode.character".
Extract Constant Unicode.numeric_value => "Encoding.Unicode.char_to_int".
Extract Constant Unicode.from_numeric_value => "Encoding.Unicode.char_from_int".
Extract Constant Unicode.compare => "Encoding.Unicode.cmp".
Extract Constant Unicode.case_fold => "Interop.Unicode.case_fold".

Extract Constant Unicode.all => "Interop.Unicode.all_chars".
Extract Constant Unicode.line_terminators => "Interop.Unicode.line_terminators".
Extract Constant Unicode.white_spaces => "Interop.Unicode.white_spaces".
Extract Constant Unicode.digits => "Interop.Unicode.digits".
Extract Constant Unicode.ascii_word_characters => "Interop.Unicode.ascii_word_characters".

Extract Constant Unicode.UnicodeProperty => "Interop.UnicodeProperties.unicodeProperty".
Extract Constant Unicode.unicode_property_eqdec => "Interop.UnicodeProperties.up_eq".
Extract Constant Unicode.code_points_for => "Interop.Unicode.code_points_for_property".

Extraction "Extracted.ml"  ECMA.ECMA ECMA.ECMA_u.

