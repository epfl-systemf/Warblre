From Coq Require Import ZArith Lia List ListSet Bool.
From Warblre Require Import Tactics List Result.
From Warblre Require Export Parameters.

(** The base files.

    These files contains some 'basic' definitions from the specification which
    are not directly related to regexes.
    These include mostly numeric definitions, as well as some notations.

    Importing this file will import all of the basic definitions.
*)

(* Exports all of the other 'base' files *)
From Warblre Require Export Typeclasses Characters Numeric Coercions.

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

(*  A weirdness of the specifiaction is that it sometimes defines lists whose indices start at 1 
    It turns out that theses lists are exactly the lists which are indexed using positive integers.
    Hence, we implement this behavior here, in the nat_indexer and pos_indexer.
*)
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

(** Additional datatypes which are never properly defined. *)
Inductive Direction :=
| forward
| backward.
#[refine] Instance eqdec_Direction: EqDec Direction := {}. decide equality. Defined.