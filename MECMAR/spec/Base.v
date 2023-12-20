From Coq Require Import ZArith Lia List ListSet Bool.
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
Definition positive_integer := { n: non_neg_integer | (0 < n)%nat }.
Definition nat_to_nni (n: nat): non_neg_integer := n.
Definition positive_to_non_neg (n: positive_integer): non_neg_integer := proj1_sig n.
Coercion nat_to_nni: nat >-> non_neg_integer.
Coercion positive_to_non_neg: positive_integer >-> non_neg_integer.
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
Infix ">=?" := (fun l r => Nat.leb r l) (at level 70, no associativity): nat_scope.

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

Parameter Character: Type.
Parameter CodePoint: Type.
Module Character.
  Parameter eqs: forall (l r: Character), {l = r} + {l <> r}.
  Parameter eqb: forall (l r: Character), bool.
  Definition neqb (l r: Character) := negb (eqb l r).

  Parameter numeric_value: Character -> non_neg_integer.
  Parameter from_numeric_value: non_neg_integer -> Character.
  Parameter code_point: Character -> CodePoint.

  Axiom numeric_pseudo_bij: forall c, Character.from_numeric_value (Character.numeric_value c) = c.

  Module Unicode.
    Parameter case_fold: Character -> Character.
  End Unicode.
End Character.
Module CodePoint.
    Parameter to_upper_case: CodePoint -> CodePoint.
    Parameter code_points_to_string: CodePoint -> list Character.
End CodePoint.

Module Characters.
  Definition NULL: Character := Character.from_numeric_value 0.
  Definition BACKSPACE: Character := Character.from_numeric_value 8.
  Definition CHARACTER_TABULATION: Character := Character.from_numeric_value 9.
  Definition LINE_FEED: Character := Character.from_numeric_value 10.
  Definition LINE_TABULATION: Character := Character.from_numeric_value 11.
  Definition FORM_FEED: Character := Character.from_numeric_value 12.
  Definition CARRIAGE_RETURN: Character := Character.from_numeric_value 13.
  Definition HYPHEN_MINUS: Character := Character.from_numeric_value 55.
End Characters.

Parameter GroupName: Type.
Module GroupName.
  Parameter eqs: forall (l r: Character), {l = r} + {l <> r}.
  Parameter eqb: forall (l r: Character), bool.
  Definition neqb (l r: Character) := negb (eqb l r).
End GroupName.

Declare Scope Character_scope.
Delimit Scope Character_scope with Chr.
Infix "=?" := Character.eqb (at level 70): Character_scope.
Infix "!=?" := Character.neqb (at level 70): Character_scope.

Declare Scope GroupName_scope.
Delimit Scope GroupName_scope with GrName.
Infix "=?" := GroupName.eqb (at level 70): GroupName_scope.
Infix "!=?" := GroupName.neqb (at level 70): GroupName_scope.

Module CompileError.
  (* https://github.com/coq/coq/issues/7424 *)
  Inductive type: let t := Type in t :=
  | AssertionFailed.
End CompileError.
Notation CompileError := CompileError.type.

Module MatchError.
  Inductive type :=
  | OutOfFuel
  | AssertionFailed.
End MatchError.
Notation MatchError := MatchError.type.

#[export]
Instance compile_assertion_error: Result.AssertionError CompileError := { f := CompileError.AssertionFailed }.
#[export]
Instance match_assertion_error: Result.AssertionError MatchError := { f := MatchError.AssertionFailed }.
Notation compile_assertion_failed := (Failure CompileError.AssertionFailed).
Notation failure := None (only parsing).
Notation out_of_fuel := (Failure MatchError.OutOfFuel).
Notation match_assertion_failed := (Failure MatchError.AssertionFailed).

(*  A CharSet is a mathematical set of characters. In the context of a Unicode pattern, “all characters” means
    the CharSet containing all code point values; otherwise “all characters” means the CharSet containing all
    code unit values. *)
Definition CharSet := list Character.

Module CharSet.
  Definition empty: CharSet := nil.
  Definition union (l r: CharSet): CharSet := ListSet.set_union Character.eqs l r.
  Definition singleton (c: Character): CharSet := c :: nil.
  Definition size (s: CharSet): nat := List.length s.
  Definition unique {F: Type} {_: Result.AssertionError F} (s: CharSet): Result Character F :=
    match s with
    | c :: nil => Success c
    | _ => Result.assertion_failed
    end.
  Definition remove_all (l r: CharSet): CharSet := ListSet.set_diff Character.eqs l r.
  Definition exist (s: CharSet) (m: Character -> Result bool MatchError): Result bool MatchError :=
    List.Exists.exist s m.
  Definition is_empty (s: CharSet): bool :=
    match s with
    | nil => true
    | _ :: _ => false
    end.
  Definition filter {F: Type} {_: Result.AssertionError F} (s: CharSet) (f: Character -> Result bool F): Result CharSet F :=
    List.Filter.filter s f.

  Definition contains (s: CharSet) (c: Character): bool := ListSet.set_mem Character.eqs c s.

  Definition range (l h: nat): CharSet :=
    List.map Character.from_numeric_value (List.Range.Nat.Bounds.range l (S h)).

  Parameter all: CharSet.
  Parameter line_terminators: CharSet.
  Parameter digits: CharSet.
  Parameter white_spaces: CharSet.
  Parameter ascii_word_characters: CharSet.
End CharSet.


(* Module IdSet.
  Parameter t: Type.

  Parameter empty: t.
  Parameter union: t -> t -> t.
  Parameter add: IdentifierName -> t -> t.
  Parameter fold: forall {T: Type}, (IdentifierName -> T -> T) -> t -> T -> T.
End IdSet. *)

(* Module DMap.
  Parameter t: Type -> Type.

  Parameter empty: forall T, t T.
  Parameter add: forall {T: Type}, IdentifierName -> T -> t T -> t T.
  Parameter remove: forall {T: Type}, IdentifierName -> t T -> t T.
  (* Parameter removeAll: forall {T: Type}, t T -> IdSet.t -> t T. *)
End DMap. *)

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
  index_using := fun T F f ls i => @List.Indexing.Nat.indexing T F f ls (proj1_sig i - 1);
  update_using := fun T F f ls i v => @List.Update.Nat.One.update T F f v ls (proj1_sig i - 1);
}.
#[export]
Instance int_indexer: Indexer Z := {
  index_using := @List.Indexing.Int.indexing;
  update_using := fun T F f ls i v => Result.assertion_failed;
}.

Notation "ls '[' i ']'" := (indexing ls i) (at level 98, left associativity).
Notation "'set' ls '[' i ']' ':=' v 'in' z" := (let! ls: list _ =<< update ls i v in z) (at level 200, ls at level 97, i at level 90, right associativity).
Notation "'set' ls '[' s '---' e ']' ':=' v 'in' z" := (let! ls: list _ =<< List.Update.Nat.Batch.update v ls (List.Range.Nat.Bounds.range (s - 1) (e - 1)) in z) (at level 200, ls at level 97, s at level 90, e at level 90, right associativity).

Notation "m 'is' p" := (match m with | p => true | _ => false end) (at level 100, p pattern, no associativity).
Notation "m 'is' 'not' p" := (match m with | p => false | _ => true end) (at level 100, p pattern, no associativity).

Module Coercions.
  Coercion wrap_result := fun (F: Type) (v: non_neg_integer) => @Success _ F v.
End Coercions.

