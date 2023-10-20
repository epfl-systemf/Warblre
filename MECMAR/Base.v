From Coq Require Import ZArith.
From Warblre Require Import Result.

(* 5.2.5 Mathematical Operations
   «  Mathematical values: Arbitrary real numbers, used as the default numeric type. »
   «  When the term integer is used in this specification, it refers to a mathematical 
      value which is in the set of integers, unless otherwise stated. When the term integral 
      Number is used in this specification, it refers to a Number value whose mathematical
      value is in the set of integers. »
   ... so, that should be a Real? (note that "integers" redirects to the second definition).
*)
Definition integer := Z.
Definition non_neg_integer := nat.
Definition non_neg_integer_or_inf := option nat.

Infix "=?" := Z.eqb (at level 70): Z_scope.
Infix "<?" := Z.ltb (at level 70): Z_scope.
Infix "<=?" := Z.leb (at level 70): Z_scope.
Infix ">?" := Z.gtb (at level 70): Z_scope.
Infix ">=?" := Z.geb (at level 70): Z_scope.

Inductive MatchFailure :=
| Mismatch
| OutOfFuel
| AssertionFailed.

Definition list_get_Z {T: Type} (ls: list T) (i: Z): Result.Result T MatchFailure := match i with
| Z0 => Result.from_option (List.nth_error ls 0) AssertionFailed
| Zpos i => Result.from_option (List.nth_error ls (Pos.to_nat i)) AssertionFailed
| Zneg _ => Result.Failure AssertionFailed
end.

Notation "ls '[' i ']'" := (list_get_Z ls i) (at level 98, left associativity).

Notation "'+∞'" := (@None nat).

Notation "m 'is' p" := (match m with | p => true | _ => false end) (at level 100, p pattern, no associativity).
Notation "m 'is' 'not' p" := (match m with | p => false | _ => true end) (at level 100, p pattern, no associativity).

(* Notation "x '<=' y" := (Z.compare x y = Lt \/ Z.compare x y = Eq). *)

(* We cheat about identifiers for now *)
Parameter IdentifierName : Type.

Module IdSet.
  Parameter t: Type.

  Parameter empty: t.
  Parameter union: t -> t -> t.
  Parameter add: IdentifierName -> t -> t.
  Parameter fold: forall {T: Type}, (IdentifierName -> T -> T) -> t -> T -> T.
End IdSet.

Module DMap.
  Parameter t: Type -> Type.

  Parameter empty: forall T, t T.
  Parameter add: forall {T: Type}, IdentifierName -> T -> t T -> t T.
  Parameter remove: forall {T: Type}, IdentifierName -> t T -> t T.
  (* Parameter removeAll: forall {T: Type}, t T -> IdSet.t -> t T. *)
End DMap.

Parameter Character: Type.