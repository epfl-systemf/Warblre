From Coq Require Import List Program.Equality.
From Warblre Require Import Base Notation.

(** 22.2.1 Patterns *)
Module Patterns.
  Inductive QuantifierPrefix :=
  | Star
  | Plus
  | Question
  | RepExact (count: non_neg_integer)
  | RepPartialRange (min: non_neg_integer)
  | RepRange (min: non_neg_integer) (max: non_neg_integer) (inv: (min <=? max)%nat = true).

(*   Module QuantifierPrefix.
    Definition eqb (l r: QuantifierPrefix): {l = r} + {~ l = r}.
    Proof. repeat decide equality. Defined.
  End QuantifierPrefix. *)

  Inductive Quantifier :=
  | Greedy (p: QuantifierPrefix)
  | Lazy (p: QuantifierPrefix).

(*   Module Quantifier.
    Definition eqb (l r: Quantifier): {l = r} + {~ l = r}.
    Proof. decide equality; apply QuantifierPrefix.eqb. Defined.
  End Quantifier. *)

(*   Module ClassAtom.
    Definition eqb (l r: ClassAtom): {l = r} + {~ l = r}.
    Proof. decide equality. apply Character.eqb. Defined.
  End ClassAtom. *)

  Inductive ClassRanges :=
  | EmptyCR
  | AtomChar (chr: Character)
  (* Escapes: \b \w ...*)
  (*| AtomHead (atom: ClassRanges) (rem: ClassRanges)
  | RangeHead (from to: ClassRanges) (rem: ClassRanges)*).

(*   Module ClassRanges.
    Definition eqb (l r: ClassRanges): {l = r} + {~ l = r}.
    Proof. decide equality; apply ClassAtom.eqb. Defined.
  End ClassRanges. *)

  Inductive CharacterClass :=
  | PositiveCC (crs: ClassRanges)
  | NegativeCC (crs: ClassRanges).

(*   Module CharacterClass.
    Definition eqb (l r: CharacterClass): {l = r} + {~ l = r}.
    Proof. decide equality; apply ClassRanges.eqb. Defined.
  End CharacterClass. *)

  Inductive Regex :=
  | Empty
  | Char (chr: Character)
  | Disjunction (r1 r2: Regex)
  | Quantified (r: Regex) (q: Quantifier)
  | Seq (r1 r2: Regex)
  | Group (name: option GroupName) (r: Regex)
  (* Assertions: ^ $ \b \B *)
  | Lookahead (r: Regex)
  | NegativeLookahead (r: Regex)
  | Lookbehind (r: Regex)
  | NegativeLookbehind (r: Regex)
  | BackReference (id: positive_integer).

  Inductive RegexContextLayer :=
  | Disjunction_left (r: Regex)
  | Disjunction_right (l: Regex)
  | Quantified_inner (q: Quantifier)
  | Seq_left (r: Regex)
  | Seq_right (l: Regex)
  | Group_inner (name: option GroupName)
  | Lookahead_inner
  | NegativeLookahead_inner
  | Lookbehind_inner
  | NegativeLookbehind_inner.

  Notation RegexContext := (list RegexContextLayer).
  (* Definition Node: Type := RegexTree * RegexContext. *)

  Fixpoint zip (focus: Regex) (ctx: RegexContext): Regex :=
    match ctx with
    | nil => focus
    | h :: t =>
      zip (match h with
      | Disjunction_left r => Disjunction focus r
      | Disjunction_right l => Disjunction l focus
      | Quantified_inner q => Quantified focus q
      | Seq_left r => Seq focus r
      | Seq_right l => Seq l focus
      | Group_inner name => Group name focus
      | Lookahead_inner => Lookahead focus
      | NegativeLookahead_inner => NegativeLookahead focus
      | Lookbehind_inner => Lookbehind focus
      | NegativeLookbehind_inner => NegativeLookbehind focus
      end) t
    end.

  Definition Root (r f: Regex) (ctx: RegexContext) := r = zip f ctx.

  Module Root.
    Lemma id: forall r, Root r r nil.
    Proof. intros. reflexivity. Qed.
  End Root.

  Module Zip.
    Lemma concat: forall ctx0 ctx1 r, (zip (zip r ctx0) ctx1) = zip r (ctx0 ++ ctx1).
    Proof.
      induction ctx0; intros ctx1 r.
      - reflexivity.
      - cbn. rewrite IHctx0. reflexivity.
    Qed.

    Lemma focus_injection: forall ctx r0 r1, zip r0 ctx = zip r1 ctx -> r0 = r1.
    Proof.
      induction ctx; intros r0 r1 Ineq.
      - assumption.
      - cbn in Ineq.
        specialize IHctx with (1 := Ineq); destruct a; injection IHctx as ->; reflexivity.
    Qed.

    Lemma focus_bijection: forall ctx r0 r1, zip r0 ctx = zip r1 ctx <-> r0 = r1.
    Proof. intros. split; intros. - eapply focus_injection. eassumption. - subst. reflexivity. Qed.

    Module Down.
      Lemma disjunction_left: forall root r f ctx, Root root (Disjunction f r) ctx -> Root root f (Disjunction_left r :: ctx).
      Proof. intros. cbn. assumption. Qed.
      Lemma disjunction_right: forall root l f ctx, Root root (Disjunction l f) ctx -> Root root f (Disjunction_right l :: ctx).
      Proof. intros. cbn. assumption. Qed.

      Lemma seq_left: forall root r f ctx, Root root (Seq f r) ctx -> Root root f (Seq_left r :: ctx).
      Proof. intros. cbn. assumption. Qed.
      Lemma seq_right: forall root l f ctx, Root root (Seq l f) ctx -> Root root f (Seq_right l :: ctx).
      Proof. intros. cbn. assumption. Qed.

      Lemma quantified_inner: forall root q f ctx, Root root (Quantified f q) ctx -> Root root f (Quantified_inner q :: ctx).
      Proof. intros. cbn. assumption. Qed.
      Lemma group_inner: forall root id f ctx, Root root (Group id f) ctx -> Root root f (Group_inner id :: ctx).
      Proof. intros. cbn. assumption. Qed.

      Lemma lookahead_inner: forall root f ctx, Root root (Lookahead f) ctx -> Root root f (Lookahead_inner :: ctx).
      Proof. intros. cbn. assumption. Qed.
      Lemma negativeLookahead_inner: forall root f ctx, Root root (NegativeLookahead f) ctx -> Root root f (NegativeLookahead_inner :: ctx).
      Proof. intros. cbn. assumption. Qed.
      Lemma lookbehind_inner: forall root f ctx, Root root (Lookbehind f) ctx -> Root root f (Lookbehind_inner :: ctx).
      Proof. intros. cbn. assumption. Qed.
      Lemma negativeLookbehind_inner: forall root f ctx, Root root (NegativeLookbehind f) ctx -> Root root f (NegativeLookbehind_inner :: ctx).
      Proof. intros. cbn. assumption. Qed.
    End Down.

    Create HintDb down.
    #[export]
    Hint Resolve Down.disjunction_left Down.disjunction_right: down.
    #[export]
    Hint Resolve Down.seq_left Down.seq_right: down.
    #[export]
    Hint Resolve Down.quantified_inner Down.group_inner: down.
    #[export]
    Hint Resolve Down.lookahead_inner Down.negativeLookahead_inner Down.lookbehind_inner Down.negativeLookbehind_inner: down.

    Ltac down := auto with down.
  End Zip.

(*   Inductive ZippedRegexPattern :=
  | Empty
  | Char (chr: Character)
  | Disjunction (r1 r2: Regex)
  | Quantified (r: Regex) (q: Quantifier)
  | Seq (r1 r2: Regex)
  | Group (id: nat) (r: Regex)
  (* Assertions: ^ $ \b \B *)
  | Lookahead (r: Regex)
  | NegativeLookahead (r: Regex)
  | Lookbehind (r: Regex)
  | NegativeLookbehind (r: Regex)
  | BackReference (id: nat).

  Definition down (r: Regex): ZippedRegexPattern :=
    let (r, ctx) := r in
    match r with
    | Empty_p => Empty
    | Char_p chr => Char chr
    | Disjunction_p l r => Disjunction (l, Disjunction_left r :: ctx) (r, Disjunction_right l :: ctx)
    | Quantified_p r q => Quantified (r, Quantified_inner q :: ctx) q
    | Seq_p l r => Seq (l, Seq_left r :: ctx) (r, Seq_right l :: ctx)
    | Group_p id r => Group id (r, Group_inner id :: ctx)
    | Lookahead_p r => Lookahead (r, Lookahead_inner :: ctx)
    | NegativeLookahead_p r => Lookahead (r, Lookahead_inner :: ctx)
    | Lookbehind_p r  => Lookbehind (r, Lookbehind_inner :: ctx)
    | NegativeLookbehind_p r  => NegativeLookbehind (r, NegativeLookbehind_inner :: ctx)
    | BackReference_p id  => BackReference id
    end. *)

End Patterns.
Export Patterns.