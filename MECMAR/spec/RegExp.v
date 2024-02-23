From Warblre Require Import Numeric.

(** 22.2.2.1.1 RegExp Records *)
Module RegExp.
  Record RegExp := reg_exp {
    ignoreCase: bool;
    multiline: bool;
    dotAll: bool;
    unicode: bool;
    capturingGroupsCount: non_neg_integer;
  }.
End RegExp.
Export RegExp.