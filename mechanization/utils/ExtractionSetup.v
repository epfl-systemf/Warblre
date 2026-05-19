(** Extract from Rocq to OCaml for Melange. 

    We will use these extraction directives twice:
    - Once for "regular" OCaml;
    - Once for OCaml aiming at being compiled by Melange;
    The key difference between these two is that the type BigInt
    is itself instantiated in two different manners, using
    zarith and Js.BigInt respectively.
*)

From Warblre Require Import Result Base API.
From Stdlib Require Import ZArith.

From Stdlib Require Extraction.
Extraction Language OCaml.
Set Extraction Output Directory ".".

From Stdlib Require extraction.ExtrOcamlBasic.
From Stdlib Require extraction.ExtrOcamlString.

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
(* Due to the split of the library into Corelib.BindNums.PosDef and
   Stdlib.PArith.BindPos, we duplicate all extractions directives to prevent
   any unexpcted behaviors where a call unexpectedly end up being in a library
   rather than the other.
*)
Extract Inductive positive =>
    "BigInt.t"
    [ "(fun p-> BigInt.add BigInt.one (BigInt.shift_left p 1))" "(fun p-> BigInt.shift_left p 1)" "BigInt.one" ]
    "Interop.erased".

Extract Constant Corelib.BinNums.PosDef.Pos.succ => "BigInt.Nat.succ".
Extract Constant Stdlib.PArith.BinPos.Pos.succ => "BigInt.Nat.succ".
Extract Inlined Constant Corelib.BinNums.PosDef.Pos.add => "BigInt.add".
Extract Inlined Constant Stdlib.PArith.BinPos.Pos.add => "BigInt.add".
Extract Inlined Constant Corelib.BinNums.PosDef.Pos.eqb => "BigInt.equal".
Extract Inlined Constant Stdlib.PArith.BinPos.Pos.add => "BigInt.add".
Extract Constant Corelib.BinNums.PosDef.Pos.compare =>
    "(fun n m -> if BigInt.equal n m then Eq else (if BigInt.lt n m then Lt else Gt))".
Extract Constant Stdlib.PArith.BinPos.Pos.compare =>
    "(fun n m -> if BigInt.equal n m then Eq else (if BigInt.lt n m then Lt else Gt))".
Extract Inlined Constant Corelib.BinNums.PosDef.Pos.to_nat => "(fun x -> x)".
Extract Inlined Constant Stdlib.PArith.BinPos.Pos.to_nat => "(fun x -> x)".
Extract Constant eqdec_positive => "BigInt.equal".

Extract Constant Corelib.BinNums.PosDef.Pos.add_carry => "Interop.erased".
Extract Constant Stdlib.PArith.BinPos.Pos.add_carry => "Interop.erased".
Extract Constant Corelib.BinNums.PosDef.Pos.pred_double => "Interop.erased".
Extract Constant Stdlib.PArith.BinPos.Pos.pred_double => "Interop.erased".
Extract Constant Corelib.BinNums.PosDef.Pos.compare_cont => "Interop.erased".
Extract Constant Stdlib.PArith.BinPos.Pos.compare_cont => "Interop.erased".
Extract Constant Corelib.BinNums.PosDef.Pos.iter_op => "Interop.erased".
Extract Constant Stdlib.PArith.BinPos.Pos.iter_op => "Interop.erased".
Extract Constant Corelib.BinNums.PosDef.Pos.of_succ_nat => "Interop.erased".
Extract Constant Stdlib.PArith.BinPos.Pos.of_succ_nat => "Interop.erased".

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

Extraction "Extracted.ml" API.
