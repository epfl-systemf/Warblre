(**
    Extract from Coq to OCaml for Melange.
    The main difference with the extraction for (pure) OCaml
    is that we don't extract to int, but to Js.BigInt.

    The reason for that is that we may need to do fuel computation
    going over the maximal safe int (before losing precision) in JS.

    We use Interop.erase to ensure that inefficient operations are not used.
*)

From Warblre Require Import Result Base API.
From Coq Require Import ZArith.

From Coq Require Extraction.
Extraction Language OCaml.

From Coq Require extraction.ExtrOcamlBasic.
From Coq Require extraction.ExtrOcamlString.

(** nat *)
Extract Inductive nat => "BigInt.t" [ "BigInt.zero" "BigInt.Nat.succ" ]
 "(fun fO fS n -> if BigInt.equal n BigInt.zero then fO () else fS (BigInt.Nat.pred n))".
Extract Inlined Constant plus => "BigInt.add".
Extract Constant pred => "BigInt.Nat.pred".
Extract Constant mult => "BigInt.mult".
Extract Inlined Constant max => "BigInt.max".
Extract Inlined Constant min => "BigInt.min".
Extract Inlined Constant Nat.eqb => "BigInt.equal".
Extract Inlined Constant EqNat.eq_nat_decide => "BigInt.equal".
Extract Inlined Constant Peano_dec.eq_nat_dec => "BigInt.equal".
Extract Inlined Constant Nat.modulo => "BigInt.rem".

Extract Constant leb => "BigInt.le".
Extract Inlined Constant Compare_dec.lt_dec => "BigInt.lt".
Extract Constant minus => "BigInt.Nat.min".
Extract Constant Nat.sub => "BigInt.Nat.min".

Extract Constant Nat.compare =>
 "(fun n m -> if BigInt.equal n m then Eq else (if BigInt.lt n m then Lt else Gt))".

(** positive *)
Extract Inductive positive =>
    "BigInt.t"
    [ "(fun p-> BigInt.add BigInt.one (BigInt.shift_left p 1))" "(fun p-> BigInt.shift_left p 1)" "BigInt.one" ]
    "Interop.erased".

Extract Inlined Constant Pos.succ => "BigInt.Nat.succ".
Extract Inlined Constant Pos.add => "BigInt.add".
Extract Inlined Constant Pos.eqb => "BigInt.equal".
Extract Constant Pos.compare =>
 "(fun n m -> if BigInt.equal n m then Eq else (if BigInt.lt n m then Lt else Gt))".
Extract Inlined Constant Pos.to_nat => "(fun x -> x)".

Extract Constant Pos.add_carry => "Interop.erased".
Extract Constant Pos.pred_double => "Interop.erased".
Extract Constant Pos.compare_cont => "Interop.erased".
Extract Constant Pos.iter_op => "Interop.erased".
Extract Constant Pos.of_succ_nat => "Interop.erased".

(** Z *)
Extract Inductive Z =>
    "BigInt.t"
    [ "BigInt.zero" "" "BigInt.neg" ]
    "(fun f0 fp fn z -> if BigInt.equal z BigInt.zero then f0 () else if BigInt.gt z BigInt.zero then fp z else fn (BigInt.neg z))".
Extract Constant Z.double => "(fun x -> BigInt.shift_left x 1)".
Extract Inlined Constant Z.of_nat => "(fun x -> x)".
Extract Inlined Constant Z.add => "BigInt.add".
Extract Inlined Constant Z.opp => "BigInt.neg".
Extract Inlined Constant Z.sub => "BigInt.sub".
Extract Constant Z.compare =>
 "(fun n m -> if BigInt.equal n m then Eq else (if BigInt.lt n m then Lt else Gt))".
Extract Inlined Constant Z.leb => "(<=)".
Extract Inlined Constant Z.ltb => "(<)".
Extract Inlined Constant Z.geb => "(>=)".
Extract Inlined Constant Z.gtb => "(>)".
Extract Inlined Constant Z.eqb => "BigInt.equal".
Extract Constant eqdec_Z => "BigInt.equal".

Extract Constant Z.succ_double => "Interop.erased".
Extract Constant Z.pred_double => "Interop.erased".
Extract Constant Z.pos_sub => "Interop.erased".


(** Result *)
(* Eliminate the Result monad from the extracted code. *)
Extract Inductive Result.Result =>
    "Interop.result"
    [ "Interop.success" "Interop.error" ]
    "(fun fS _ v -> fS v )".

(** Hex *)
Extract Constant HexDigit.type => "char".
Extract Constant HexDigit.eq_dec => "Char.equal".
Extract Constant HexDigit.to_integer => "Interop.parse_hex".

(** Ascii *)
Extract Constant AsciiLetter.type => "char".
Extract Constant AsciiLetter.eq_dec => "Char.equal".
Extract Constant AsciiLetter.numeric_value => "(fun c -> Host.of_int (Char.code c))".

Extraction "Extracted.ml" API.