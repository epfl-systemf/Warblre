From Warblre Require Import Numeric.

(** >>
    22.2.2.1.1 RegExp Records

    A RegExp Record is a Record value used to store information about a RegExp that is needed during compilation and possibly during matching.

    It has the following fields:
<<*)
(** >>
  WILDCARD PARSING_FILE_END
<<*)
Module RegExpRecord.
  Record type := make {
    (*>> [[IgnoreCase]] <<*)
    ignoreCase: bool;
    (*>> [[Multiline]] <<*)
    multiline: bool;
    (*>> [[DotAll]] <<*)
    dotAll: bool;
    (*>> [[Unicode]] <<*)
    unicode: unit;
    (*>> [[CapturingGroupsCount]] <<*)
    capturingGroupsCount: non_neg_integer;
  }.
End RegExpRecord.
Notation RegExpRecord := RegExpRecord.type.
Notation reg_exp_record := RegExpRecord.make.