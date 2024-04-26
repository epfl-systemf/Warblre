From Warblre Require Import Numeric.

(** 22.2.2.1.1 RegExp Records *)
Module RegExpRecord.
  Record type := make {
    ignoreCase: bool;
    multiline: bool;
    dotAll: bool;
    unicode: unit;
    capturingGroupsCount: non_neg_integer;
  }.
End RegExpRecord.
Notation RegExpRecord := RegExpRecord.type.
Notation reg_exp_record := RegExpRecord.make.