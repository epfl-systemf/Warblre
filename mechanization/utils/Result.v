Declare Scope result_flow.

Inductive Result (S F: Type) :=
| Success (s: S)
| Error (f: F).
Arguments Success {S F} s.
Arguments Error {S F} f.

Module Result.

  Class AssertionError (F: Type) := { f: F }.

  Definition ret {T: Type} (F: Type) (v: T): Result T F := @Success _ F v.

  Definition bind {S T F: Type} (r: Result S F) (f: S -> Result T F): Result T F := match r with
  | Success s => f s
  | Error f => Error f
  end.

  Definition map {S T F: Type} (r: Result S F) (f: S -> T): Result T F := bind r (fun s => Success (f s)).

  Lemma left_identity {S T F: Type}: forall (v: S) (f: S -> Result T F), bind (ret F v) f = f v.
  Proof. reflexivity. Qed.

  Lemma right_identity {T F: Type}: forall (m: Result T F), bind m (ret F) = m.
  Proof. intros [|]; reflexivity. Qed.

  Lemma associativity {S T U F: Type}: forall (m: Result S F) (f: S -> Result T F) (g: T -> Result U F),
    bind (bind m f) g = bind m (fun s => bind (f s) g).
  Proof. intros [|] ? ?; reflexivity. Qed.

  Definition assertion_failed {S F: Type} {failure: AssertionError F}: Result S F :=
    let (f) := failure in
    Error f.

  Ltac inject_all := repeat match goal with
  | [ H: Success _ = Success _ |- _ ] => injection H as H
  | [ H: Error _   = Error _   |- _ ] => injection H as H
  | [ _: Success _ = Error _   |- _ ] => discriminate
  | [ _: Error _   = Success _ |- _ ] => discriminate
  end.

  Ltac assertion_failed_helper := repeat
  (   unfold Result.assertion_failed in *
  ||  match goal with
      | [ f: AssertionError _ |- _ ] => destruct f as [f]
      | [ E: {| f := _ |} = {| f := _ |} |- _ ] => injection E as ->
      | [ E: Error _ = Error _ |- _ ] => injection E as ->
      end); try easy.

  Module Conversions.
    Definition from_option {S F: Type} {failure: AssertionError F} (o: option S): Result S F := match o with
    | Some x => Success x
    | None => assertion_failed
    end.
  End Conversions.

  Module Notations.
    Notation "'let!' r '=<<' y 'in' z" := (bind y (fun r => z))
      (at level 20, r pattern, y at level 100, z at level 200): result_flow.

    Notation "'assert!' b ';' z" := (if (negb b) then assertion_failed else z) (at level 20, b at level 100, z at level 100): result_flow.

    Notation "'destruct!' r '<-' y 'in' z" := (match y with
      | r => z
      | _ => assertion_failed (* Otherwise, consider the failure as an assertion failure *)
      end)
      (at level 20, r pattern, y at level 100, z at level 200): result_flow.

    Module Boolean.
      Notation "'if!' b 'then' tf 'else' ff" := (match (b: Result bool _) with
      | Success true => tf
      | Success false => ff
      | Error f => Error f
      end) (at level 20, b at level 100, tf at level 100, ff at level 100): result_flow.

      Notation "l '&&!' r" := (match (l: Result bool _) with
      | Success true => (r: Result bool _)
      | Success false => Success false
      | Error f => Error f
      end) (at level 40, left associativity): result_flow.

      Notation "l '||!' r" := (match (l: Result bool _) with
      | Success true => Success true
      | Success false => (r: Result bool _)
      | Error f => Error f
      end) (at level 50, left associativity): result_flow.
    End Boolean.
  End Notations.
End Result.

From Warblre Require Import Typeclasses.
#[refine] Instance eqdec_result {T F: Type} `{EqDec T} `{EqDec F}: EqDec (Result T F) := {}. decide equality; apply EqDec.eq_dec. Defined.


