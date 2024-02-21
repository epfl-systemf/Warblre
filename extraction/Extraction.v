From Warblre Require Import Base Patterns Semantics ClutterFree Frontend.

From Coq Require Extraction.
Extraction Language OCaml.

From Coq Require extraction.ExtrOcamlBasic.
From Coq Require extraction.ExtrOcamlString.
From Coq Require extraction.ExtrOcamlNatInt.
From Coq Require extraction.ExtrOcamlZInt.

Extract Constant HexDigit.type => "char".
Extract Constant HexDigit.to_integer => "Interop.parse_hex".

Extract Constant AsciiLetter.type => "char".

Extract Constant Character => "Interop.character".
Extract Constant Character.numeric_value => "Interop.char_to_int".
Extract Constant Character.from_numeric_value => "Interop.char_of_int".
Extract Constant Character.Unicode.case_fold => "Interop.case_fold".
Extract Constant Character.compare => "Interop.cmp".

Extract Constant Character.all => "Interop.all_chars".
Extract Constant Character.line_terminators => "Interop.line_terminators".
Extract Constant Character.white_spaces => "Interop.white_spaces".
Extract Constant Character.digits => "Interop.digits".
Extract Constant Character.ascii_word_characters => "Interop.ascii_word_characters".

Extract Constant CodePoint => "Interop.codepoint".
Extract Constant CodePoint.code_points_to_string => "Interop.code_points_to_string".
Extract Constant CodePoint.to_upper_case => "Interop.to_upper_case".
Extract Constant CodePoint.from_ascii_letter => "Interop.ascii_letter".
Extract Constant CodePoint.from_character => "Interop.code_point".
Extract Constant CodePoint.numeric_value => "Interop.numeric_value".

Extract Constant GroupName => "int".
Extract Constant GroupName.eqb => "Int.equal".

Extract Constant Patterns.GroupName.type => "string".
Extract Constant Patterns.GroupName.eqs => "String.equal".

Extraction "Extracted.ml" Semantics.compilePattern ClutterFree.regex_match
  Frontend.PrototypeExec Frontend.PrototypeSearch Frontend.PrototypeTest Frontend.PrototypeMatch Frontend.StringPrototypeMatchAll
  Frontend.RegExpInitialize Frontend.setlastindex.

