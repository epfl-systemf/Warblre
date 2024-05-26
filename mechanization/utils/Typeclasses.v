From Warblre Require Import Retrieve.
From Coq Require Import ZArith Program.Equality Lia.

Local Close Scope nat.

Declare Scope wt_scope.
Delimit Scope wt_scope with wt.
Local Open Scope wt.

Module EqDec.
  Class type (T: Type) := make {
    eq_dec: forall (l r: T), {l=r} + {l<>r};
  }.

  Definition eqb {T: Type} `{type T} (l r: T): bool := if eq_dec l r then true else false.
  Definition neqb {T: Type} `{type T} (l r: T): bool := negb (eqb l r).

  Lemma inversion_true {T: Type} `{type T}: forall (l r: T), eqb l r = true <-> l = r.
  Proof. intros. unfold eqb. destruct (eq_dec l r) eqn:Eq; split; easy. Qed.

  Lemma inversion_false {T: Type} `{type T}: forall (l r: T), eqb l r = false <-> l <> r.
  Proof. intros. unfold eqb. destruct (eq_dec l r) eqn:Eq; split; easy. Qed.

  Lemma reflb {T: Type} `{type T}: forall (t: T), eqb t t = true.
  Proof. intros. unfold eqb. destruct (eq_dec t t) eqn:Eq; easy. Qed.
End EqDec.
Notation EqDec := EqDec.type.
Infix "=?=" := EqDec.eq_dec (at level 37, no associativity).
Infix "==" := EqDec.eqb (at level 37, no associativity).
Infix "!=" := EqDec.neqb (at level 37, no associativity).
Infix "==#" := EqDec.eq_dec (at level 70, no associativity): wt_scope.
Infix "==?" := EqDec.eqb (at level 70, no associativity): wt_scope.
Infix "!=?" := EqDec.neqb (at level 70, no associativity): wt_scope.

Instance eqdec_bool: EqDec bool := { eq_dec := Bool.bool_dec }.
Instance eqdec_nat: EqDec nat := { eq_dec := Nat.eq_dec }.
#[refine] Instance eqdec_positive: EqDec positive := {}. decide equality. Defined.
#[refine] Instance eqdec_Z: EqDec Z := {}. decide equality; apply EqDec.eq_dec. Defined.
(* The cost (10) is a band-aid fix to avoid stack overflows when resolving EqDec in some theorems (e.g. EarlyErrors.groupSpecifiersThatMatch_singleton). TODO: investigate *)
#[refine] Instance eqdec_option {T: Type} `{EqDec T}: EqDec (option T) | 10 := {}. decide equality; apply EqDec.eq_dec. Defined.
#[refine] Instance eqdec_list {T: Type} `{EqDec T}: EqDec (list T) | 10 := {}. decide equality; apply EqDec.eq_dec. Defined.

Module OrdDec.
  Definition ord_from_compare
    {T: Type} {C: T -> T -> Prop} (c: T -> T -> comparison)
    (eq_c: forall x y, c x y = Eq -> x = y) (lt_c: forall x y, c x y = Lt -> (C x y)) (gt_c: forall x y, c x y = Gt -> (C y x))
    : forall l r, {C l r} + {l = r} + {C r l} :=
    (fun l r => match c l r as ord return (c l r = ord) -> {C l r} + {l = r} + {C r l} with
    | Eq => fun eq => inleft (right (eq_c _ _ eq))
    | Lt => fun eq => inleft (left (lt_c _ _ eq))
    | Gt => fun eq => inright (gt_c _ _ eq)
    end eq_refl).

  Class type (T: Type) := make {
    SOrd: T -> T -> Prop;
    ord_dec: forall (l r: T), {SOrd l r} + {l = r} + {SOrd r l};

    s_irrefl: forall t, ~ SOrd t t;
    s_assym: forall l r, SOrd l r -> ~ SOrd r l;
    s_trans: forall l m r, SOrd l m -> SOrd m r -> SOrd l r;
    s_conn: forall l r, l <> r -> (SOrd l r \/ SOrd r l);
  }.

  Inductive Ord {T: Type} `{type T}: T -> T -> Prop :=
  | Eq: forall (l r: T), l = r -> Ord l r
  | Lt: forall (l r: T), SOrd l r -> Ord l r.

  Infix "<" := OrdDec.SOrd (at level 70).
  Infix "<=" := OrdDec.Ord (at level 70).
  Notation "l > r" := (OrdDec.SOrd r l) (at level 70, only parsing).
  Notation "l >= r" := (OrdDec.Ord r l) (at level 70, only parsing).

  Context {T: Type} `{type T}.

  Theorem sord_neg_elim: forall (l r: T), ~ (l < r) -> r < l \/ l = r.
  Proof.
    intros l r nOrd_l_r.
    destruct (ord_dec r l) as [ [ ? | -> ] | ? ].
    - left. assumption.
    - right. reflexivity.
    - contradiction.
  Qed.

  Theorem ord_alternative: forall (l r: T), l <= r <-> ~ (r < l).
  Proof.
    intros l r; split; intros H.
    - dependent destruction H.
      + subst. apply s_irrefl.
      + apply s_assym. assumption.
    - apply sord_neg_elim in H as [ ? | -> ].
      + apply Lt. assumption.
      + apply Eq. reflexivity.
  Qed.

  Lemma refl: forall (t: T), t <= t.
  Proof. intros t. apply Eq. reflexivity. Qed.

  Lemma trans: forall (l m r: T), l <= m -> m <= r -> l <= r.
  Proof.
    intros l m r Hl Hr; inversion Hl; inversion Hr; subst; try assumption.
    apply Lt. apply s_trans with (m := m); assumption.
  Qed.

  Lemma antisym: forall (l r: T), l <= r -> r <= l -> l = r.
  Proof.
    intros l r Hl Hr; inversion Hl; inversion Hr; subst; try reflexivity.
    ltac2:(retrieve (SOrd l r) as Falsum).
    apply s_assym in Falsum. contradiction.
  Qed.

  Lemma strong_conn: forall (l r: T), l <= r \/ r <= l.
  Proof.
    intros l r.
    destruct (ord_dec l r) as [ [ ? | -> ] | ? ].
    + left. apply Lt. assumption.
    + left. apply Eq. reflexivity.
    + right. apply Lt. assumption.
  Qed.

  Definition lt_dec (l r: T): {l < r} + {l >= r}.
    destruct (ord_dec r l) as [ [ SOrd_l_r | -> ] | SOrd_r_l ].
    - right. apply Lt. assumption.
    - right. apply refl.
    - left. assumption.
  Qed.

  Definition le_dec (l r: T): {l <= r} + {l > r}.
    destruct (ord_dec r l) as [ [ SOrd_l_r | -> ] | SOrd_r_l ].
    - right. assumption.
    - left. apply refl.
    - left. apply Lt. assumption.
  Qed.

  Definition gt_dec (l r: T): {l > r} + {l <= r} := Sumbool.sumbool_not _ _ (le_dec l r).
  Definition ge_dec (l r: T): {l >= r} + {l < r} := Sumbool.sumbool_not _ _ (lt_dec l r).
End OrdDec.
Notation OrdDec := OrdDec.type.

Infix "<" := OrdDec.SOrd (at level 70): wt_scope.
Infix "<=" := OrdDec.Ord (at level 70): wt_scope.
Notation "l > r" := (OrdDec.SOrd r l) (at level 70, only parsing): wt_scope.
Notation "l >= r" := (OrdDec.Ord r l) (at level 70, only parsing): wt_scope.

Infix "<#" := OrdDec.lt_dec (at level 35): wt_scope.
Infix "<=#" := OrdDec.le_dec (at level 35): wt_scope.
Infix ">#" := OrdDec.gt_dec (at level 35): wt_scope.
Infix ">=#" := OrdDec.ge_dec (at level 35): wt_scope.

(* These would make more sense at level ~35, but Coq's stdlib decided otherwise. *)
Infix "<?" := OrdDec.lt_dec (at level 70): wt_scope.
Infix "<=?" := OrdDec.le_dec (at level 70): wt_scope.
Infix ">?" := OrdDec.gt_dec (at level 70): wt_scope.
Infix ">=?" := OrdDec.ge_dec (at level 70): wt_scope.

#[refine]
Instance ordeq_positive: OrdDec positive := {
  SOrd := Pos.lt;
  ord_dec := OrdDec.ord_from_compare Pos.compare _ _ _;
}.
all: try lia.
- apply POrderedType.Positive_as_OT.compare_eq.
- apply POrderedType.Positive_as_OT.compare_lt_iff.
- apply POrderedType.Positive_as_OT.compare_gt_iff.
Defined.

#[refine]
Instance ordeq_nat: OrdDec nat := {
  SOrd := lt;
  ord_dec := OrdDec.ord_from_compare Nat.compare _ _ _;
}.
all: try lia.
- apply Nat.compare_eq_iff.
- apply Nat.compare_lt_iff.
- apply Nat.compare_gt_iff.
Defined.

#[refine]
Instance ordeq_N: OrdDec N := {
  SOrd := N.lt;
  ord_dec := OrdDec.ord_from_compare N.compare _ _ _;
}.
all: try lia.
- apply N.compare_eq_iff.
- apply N.compare_lt_iff.
- apply N.compare_gt_iff.
Defined.

#[refine]
Instance ordeq_Z: OrdDec Z := {
  SOrd := Z.lt;
  ord_dec := OrdDec.ord_from_compare Z.compare _ _ _;
}.
all: try lia.
- apply Z.compare_eq_iff.
- apply Z.compare_lt_iff.
- apply Z.compare_gt_iff.
Defined.