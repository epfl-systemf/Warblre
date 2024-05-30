From Warblre Require Import Result Base API.
From Coq Require Import ZArith.

From Coq Require Extraction.
Extraction Language OCaml.

From Coq Require extraction.ExtrOcamlBasic.
From Coq Require extraction.ExtrOcamlString.
From Coq Require extraction.ExtrOcamlNatInt.
From Coq Require extraction.ExtrOcamlZInt.
Extract Constant Pos.to_nat => "(fun c -> c)".

(** Result *)
(* Eliminate the Result monad from the extracted code. *)
(* If Failure was to be constructed in Coq, an exception will be thrown instead in OCaml. *)
Extract Inductive Result.Result =>
    "Interop.result"
    [ "Interop.success" "Interop.failure" ]
    "(fun fS _ v -> fS v )".

(** Hex *)
Extract Constant HexDigit.type => "char".
Extract Constant HexDigit.eq_dec => "Char.equal".
Extract Constant HexDigit.to_integer => "Interop.parse_hex".

(** Ascii *)
Extract Constant AsciiLetter.type => "char".
Extract Constant AsciiLetter.eq_dec => "Char.equal".
Extract Constant AsciiLetter.numeric_value => "Char.code".

Extraction "Extracted.ml" API.