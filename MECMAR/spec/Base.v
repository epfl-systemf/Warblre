From Coq Require Import ZArith Lia.
From Warblre Require Import Tactics List Result.

Import Result.Notations.
Local Open Scope result_flow.

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
Definition nat_to_nni(n: nat): non_neg_integer := n.
Coercion nat_to_nni: nat >-> non_neg_integer.
(* Nat or Infinity *)
Module NoI.
  Inductive non_neg_integer_or_inf :=
  | N (n: non_neg_integer)
  | Inf.

  Definition eqb (l r: non_neg_integer_or_inf): bool := match l, r with
  | N l', N r' => Nat.eqb l' r'
  | Inf, Inf => true
  | _, _ => false
  end.

  Definition add (l r: non_neg_integer_or_inf): non_neg_integer_or_inf := match l, r with
  | N l', N r' => N (Nat.add l' r')
  | _, _ => Inf
  end.

  Definition sub (l: non_neg_integer_or_inf) (r: non_neg_integer): non_neg_integer_or_inf := match l with
  | N l' => N (Nat.sub l' r)
  | _=> Inf
  end.

  Definition leqb (l: non_neg_integer) (r: non_neg_integer_or_inf): bool := match r with
  | N r' => (l <=? r')%nat
  | Inf => true
  end.

  Module Coercions.
    Coercion NoI.N: non_neg_integer >-> non_neg_integer_or_inf.
  End Coercions.
End NoI.
Notation "'+∞'" := NoI.Inf.
Export NoI(non_neg_integer_or_inf).

Infix "!=?" := (fun l r => negb (Nat.eqb l r)) (at level 70): nat_scope.
Infix "<=?" := Nat.leb (at level 70, no associativity): nat_scope.

Declare Scope NoI_scope.
Delimit Scope NoI_scope with NoI.
Infix "=?" := NoI.eqb (at level 70): NoI_scope.
Infix "+" := NoI.add (at level 50, left associativity): NoI_scope.
Infix "-" := NoI.sub (at level 50, left associativity): NoI_scope.
Infix "<=?" := NoI.leqb (at level 70, no associativity): NoI_scope.

Infix "=?" := Z.eqb (at level 70): Z_scope.
Infix "!=?" := (fun l r => negb (Z.eqb l r)) (at level 70): Z_scope.
Infix "<?" := Z.ltb (at level 70): Z_scope.
Infix "<=?" := Z.leb (at level 70): Z_scope.
Infix ">?" := Z.gtb (at level 70): Z_scope.
Infix ">=?" := Z.geb (at level 70): Z_scope.

Inductive MatchError :=
| OutOfFuel
| AssertionFailed.


(* We cheat about identifiers for now *)
Notation IdentifierName := Z.


Module IdSet.
  Parameter t: Type.

  Parameter empty: t.
  Parameter union: t -> t -> t.
  Parameter add: IdentifierName -> t -> t.
  Parameter fold: forall {T: Type}, (IdentifierName -> T -> T) -> t -> T -> T.
End IdSet.

(* Module DMap.
  Parameter t: Type -> Type.

  Parameter empty: forall T, t T.
  Parameter add: forall {T: Type}, IdentifierName -> T -> t T -> t T.
  Parameter remove: forall {T: Type}, IdentifierName -> t T -> t T.
  (* Parameter removeAll: forall {T: Type}, t T -> IdSet.t -> t T. *)
End DMap. *)

Notation "ls '[' i ']'" := (List.Indexing.indexing ls i) (at level 98, left associativity).
Notation "'set' ls '[' i ']' ':=' v 'in' z" := (let! ls =<< List.Updating.updating ls i v in z) (at level 200, ls at level 97, right associativity).
Notation "'set' ls '[' is '...]' ':=' v 'in' z" := (let! ls =<< IdSet.fold (fun i rls => let! ls =<< rls in List.Updating.updating ls i v) is (Success ls) in z) (at level 200, ls at level 97, right associativity).

Notation "m 'is' p" := (match m with | p => true | _ => false end) (at level 100, p pattern, no associativity).
Notation "m 'is' 'not' p" := (match m with | p => false | _ => true end) (at level 100, p pattern, no associativity).

Parameter Character: Type.
Module Character.
  Parameter eqb: Character -> Character -> bool.
End Character.

Declare Scope Character_scope.
Delimit Scope Character_scope with Chr.
Infix "=?" := Character.eqb (at level 70): Character_scope.
