From Warblre Require Import List Result Base.

Import Result.Notations.
Local Open Scope result_flow.

(** Notations for list operations *)

Notation "ls '.[' i ']'" := (indexing ls i) (at level 1, left associativity).
Notation "'set' ls '.[' i ']' ':=' v 'in' z" := (let! ls: list _ =<< update ls i v in z) (at level 200, ls at level 0, i at level 90, right associativity).
Notation "'set' ls '.[' s '---' e ']' ':=' v 'in' z" := (let! ls: list _ =<< List.Update.Nat.Batch.update v ls (List.Range.Nat.Bounds.range (s - 1) (e - 1)) in z) (at level 200, ls at level 0, s at level 90, e at level 90, right associativity).

(** The is (not) operator *)

Notation "m 'is' p" := (match m with | p => true | _ => false end) (at level 100, p pattern, no associativity).
Notation "m 'is' 'not' p" := (match m with | p => false | _ => true end) (at level 100, p pattern, no associativity).
