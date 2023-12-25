From Coq Require Import ZArith Lia List ListSet Bool.
From Warblre Require Import Tactics List Result.
From Warblre Require Export Characters Numeric Coercions Errors.

(** Notations for list operations *)

Import Result.Notations.
Local Open Scope result_flow.

Class Indexer (I: Type) := {
  index_using: forall (T F: Type) (_: Result.AssertionError F) (ls: list T) (i: I), Result.Result T F;
  update_using: forall (T F: Type) (_: Result.AssertionError F) (ls: list T) (i: I) (v: T), Result.Result (list T) F;
}.
Definition indexing {I T F: Type} {f: Result.AssertionError F} {indexer: Indexer I} (ls: list T) (i: I) :=
  index_using T F f ls i.
Definition update {I T F: Type} {f: Result.AssertionError F} {indexer: Indexer I} (ls: list T) (i: I) (v: T) :=
  update_using T F f ls i v.

#[export]
Instance nat_indexer: Indexer nat := {
  index_using := fun T F f ls i => if (i =? 0)%nat then Result.assertion_failed else @List.Indexing.Nat.indexing T F f ls (i - 1);
  update_using := fun T F f ls i v => if (i =? 0)%nat then Result.assertion_failed else @List.Update.Nat.One.update T F f v ls (i - 1);
}.
#[export]
Instance pos_indexer: Indexer positive_integer := {
  index_using := fun T F f ls i => @List.Indexing.Nat.indexing T F f ls (positive_to_non_neg i - 1);
  update_using := fun T F f ls i v => @List.Update.Nat.One.update T F f v ls (positive_to_non_neg i - 1);
}.
#[export]
Instance int_indexer: Indexer Z := {
  index_using := @List.Indexing.Int.indexing;
  update_using := fun T F f ls i v => Result.assertion_failed; (* This operation is never used. *)
}.

Notation "ls '[' i ']'" := (indexing ls i) (at level 98, left associativity).
Notation "'set' ls '[' i ']' ':=' v 'in' z" := (let! ls: list _ =<< update ls i v in z) (at level 200, ls at level 97, i at level 90, right associativity).
Notation "'set' ls '[' s '---' e ']' ':=' v 'in' z" := (let! ls: list _ =<< List.Update.Nat.Batch.update v ls (List.Range.Nat.Bounds.range (s - 1) (e - 1)) in z) (at level 200, ls at level 97, s at level 90, e at level 90, right associativity).

(** The is (not) operator *)

Notation "m 'is' p" := (match m with | p => true | _ => false end) (at level 100, p pattern, no associativity).
Notation "m 'is' 'not' p" := (match m with | p => false | _ => true end) (at level 100, p pattern, no associativity).

