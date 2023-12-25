From Coq Require Import List Program.Equality PeanoNat.
From Warblre Require Import Notation Numeric Characters.

(** 22.2.1 Patterns *)
(* The RegExp constructor applies the following grammar to the input pattern String. An error occurs if the
  grammar cannot interpret the String as an expansion of Pattern *)
Module Patterns.

  (** GroupName :: *)
  Module GroupName.
    Parameter type: Type.
    Parameter eqs: forall (l r: type), {l = r} + {l <> r}.
    Parameter eqb: forall (l r: type), bool.
    Definition neqb (l r: type) := negb (eqb l r).
  End GroupName.
  Notation GroupName := GroupName.type.

  Declare Scope GroupName_scope.
  Delimit Scope GroupName_scope with GrName.
  Infix "=?" := GroupName.eqb (at level 70): GroupName_scope.
  Infix "!=?" := GroupName.neqb (at level 70): GroupName_scope.

  (** CharacterClassEscape :: *)
  Module CharacterClassEscape.
    Inductive type :=
    (* d *)
    | d
    (* D *)
    | D
    (* s *)
    | s
    (* S *)
    | S
    (* w *)
    | w
    (* W *)
    | W.
    (*+ TODO: Unicode property p P *)

    Definition eqs (l r: type): {l = r} + {~ l = r}.
    Proof. decide equality. Defined.
  End CharacterClassEscape.
  Notation CharacterClassEscape := CharacterClassEscape.type.

  (** ControlEscape :: *)
  Module ControlEscape.
    Inductive type :=
    (* f *)
    | f
    (* n *)
    | n
    (* r *)
    | r
    (* t *)
    | t
    (* v *)
    | v.

    Definition eqs (l r: type): {l = r} + {~ l = r}.
    Proof. decide equality. Defined.
  End ControlEscape.
  Notation ControlEscape := ControlEscape.type.

  (** CharacterEscape :: *)
  Module CharacterEscape.
    Inductive type :=
    | ControlEsc (esc: ControlEscape)
    (*+ TODO: c *)
    (* 0 *)
    | Zero
    (*+ TODO: x *)
    (*+ TODO: u *)
    | IdentityEsc (chr: Character).

    Definition eqs (l r: type): {l = r} + {~ l = r}.
    Proof. decide equality; try apply ControlEscape.eqs; try apply Character.eqs. Defined.
  End CharacterEscape.
  Notation CharacterEscape := CharacterEscape.type.

  (** ClassEscape :: *)
  Module ClassEscape.
    Inductive type :=
    (* b *)
    | b
    (* - *)
    | Dash
    | CharacterClassEsc (esc: CharacterClassEscape)
    | CharacterEsc (esc: CharacterEscape).

    Definition eqs (l r: type): {l = r} + {~ l = r}.
    Proof. decide equality; try apply CharacterClassEscape.eqs; try apply CharacterEscape.eqs. Defined.
  End ClassEscape.
  Notation ClassEscape := ClassEscape.type.

  (** AtomEscape :: *)
  Module AtomEscape.
    Inductive type :=
    | DecimalEsc (n: positive_integer)
    | CharacterClassEsc (esc: CharacterClassEscape)
    | CharacterEsc (esc: CharacterEscape)
    | GroupEsc (id: GroupName).

    Definition eqs (l r: type): {l = r} + {~ l = r}.
    Proof. decide equality; try apply CharacterClassEscape.eqs; try apply CharacterEscape.eqs; try apply GroupName.eqs; try decide equality. Defined.
  End AtomEscape.
  Notation AtomEscape := AtomEscape.type.

  (** QuantifierPrefix :: *)
  Inductive QuantifierPrefix :=
  | Star
  | Plus
  | Question
  | RepExact (count: non_neg_integer)
  | RepPartialRange (min: non_neg_integer)
  | RepRange (min: non_neg_integer) (max: non_neg_integer).
  Module QuantifierPrefix.
    Definition eqs (l r: QuantifierPrefix): {l = r} + {~ l = r}.
    Proof. decide equality; apply Nat.eq_dec. Defined.
  End QuantifierPrefix.

  (** Quantifier :: *)
  Inductive Quantifier :=
  | Greedy (p: QuantifierPrefix)
  | Lazy (p: QuantifierPrefix).
  Module Quantifier.
    Definition eqs (l r: Quantifier): {l = r} + {~ l = r}.
    Proof. decide equality; apply QuantifierPrefix.eqs. Defined.
  End Quantifier.

  (** ClassAtom :: *)
  (** ClassAtomNoDash :: *)
  Inductive ClassAtom :=
  | SourceCharacter (chr: Character)
  | ClassEsc (esc: ClassEscape).
  Module ClassAtom.
    Definition eqs (l r: ClassAtom): {l = r} + {~ l = r}.
    Proof. decide equality; try apply Character.eqs; try apply ClassEscape.eqs. Defined.
  End ClassAtom.

  (** ClassRanges :: *)
  (** NonemptyClassRanges :: *)
  (** NonemptyClassRangesNoDash :: *)
  Inductive ClassRanges :=
  | EmptyCR
  | ClassAtomCR (ca: ClassAtom) (t: ClassRanges)
  | RangeCR (l h: ClassAtom) (t: ClassRanges).
  Module ClassRanges.
    Definition eqs (l r: ClassRanges): {l = r} + {~ l = r}.
    Proof. decide equality; apply ClassAtom.eqs. Defined.
  End ClassRanges.

  (** CharacterClass :: *)
  Inductive CharClass :=
  | NoninvertedCC (crs: ClassRanges)
  | InvertedCC (crs: ClassRanges).
  Module CharClass.
    Definition eqs (l r: CharClass): {l = r} + {~ l = r}.
    Proof. decide equality; apply ClassRanges.eqs. Defined.
  End CharClass.

  (** Pattern *)
  (** Disjunction *)
  (** Alternative :: *)
  (** Term :: *)
  (** Assertion :: *)
  (** Atom :: *)
  Inductive Regex :=
  | Empty
  | Char (chr: Character)
  | Dot
  | AtomEsc (ae: AtomEscape)
  | CharacterClass (cc: CharClass)
  | Disjunction (r1 r2: Regex)
  | Quantified (r: Regex) (q: Quantifier)
  | Seq (r1 r2: Regex)
  | Group (name: option GroupName) (r: Regex)
  (*+ Assertions: ^ $ \b \B *)
  | Lookahead (r: Regex)
  | NegativeLookahead (r: Regex)
  | Lookbehind (r: Regex)
  | NegativeLookbehind (r: Regex).
  Module Regex.
    Definition eqs (l r: Regex): {l = r} + {~ l = r}.
    Proof. decide equality; try solve [
      apply Character.eqs |
      apply AtomEscape.eqs |
      apply Quantifier.eqs |
      apply CharClass.eqs |
      decide equality; apply GroupName.eqs].
    Defined.
  End Regex.

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
  Module RegexContextLayer.
    Definition eqs (l r: RegexContextLayer): {l = r} + {~ l = r}.
    Proof. decide equality; try solve [
      apply Regex.eqs |
      apply Quantifier.eqs |
      decide equality; apply GroupName.eqs].
    Defined.
  End RegexContextLayer.

  Notation RegexContext := (list RegexContextLayer).
  Module RegexContext.
    Definition eqs (l r: RegexContext): {l = r} + {~ l = r}.
    Proof. decide equality. apply RegexContextLayer.eqs. Defined.
  End RegexContext.
  Definition RegexNode: Type := Regex * RegexContext.
  Module RegexNode.
    Definition eqs (l r: RegexNode): {l = r} + {~ l = r}.
    Proof. decide equality; solve [ apply Regex.eqs | apply RegexContext.eqs ]. Defined.
  End RegexNode.

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

    Lemma nil: forall r r', Root r r' nil -> r = r'.
    Proof. intros. unfold Root in H. cbn in H. assumption. Qed.
  End Root.

  Module Zip.
    Lemma id: forall r, zip r nil = r.
    Proof. intros. reflexivity. Qed.

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

    Ltac down := eauto with down.
  End Zip.

End Patterns.
Export Patterns.