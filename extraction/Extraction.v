From Warblre Require Import Base Patterns Semantics ClutterFree Frontend.

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
Extract Constant Character.Unicode.case_fold => "Interop.case_fold".

Extract Constant CodePoint => "char".
Extract Constant CodePoint.code_points_to_string => "Interop.code_points_to_string".
Extract Constant CodePoint.to_upper_case => "Interop.to_upper_case".
Extract Constant CodePoint.from_character => "Interop.code_point".

Extract Constant GroupName => "int".
Extract Constant GroupName.eqb => "Int.equal".

Extract Constant CharSet.all => "Interop.all_chars".
Extract Constant CharSet.line_terminators => "Interop.line_terminators".
Extract Constant CharSet.white_spaces => "Interop.line_terminators".
Extract Constant CharSet.digits => "Interop.line_terminators".
Extract Constant CharSet.ascii_word_characters => "Interop.line_terminators".

Extract Constant Patterns.GroupName.type => "string".
Extract Constant Patterns.GroupName.eqs => "String.equal".

Extraction "Extracted.ml" Semantics.compilePattern ClutterFree.regex_match
  Frontend.PrototypeExec Frontend.PrototypeSearch Frontend.PrototypeTest Frontend.PrototypeMatch Frontend.StringPrototypeMatchAll
  Frontend.RegExpInitialize Frontend.setlastindex.

