From Coq Require Import List Program.Equality PeanoNat.
From Warblre Require Import List Result Notation Numeric Characters.

(** 22.2.1 Patterns *)
(* The RegExp constructor applies the following grammar to the input pattern String. An error occurs if the
  grammar cannot interpret the String as an expansion of Pattern *)
Module Patterns.

  (** GroupName :: *)
  Module GroupName.
    Parameter type: Type.
    Parameter eqs: forall (l r: type), {l = r} + {l <> r}.
    Definition eqb (l r: type) := if eqs l r then true else false.
    Definition neqb (l r: type) := negb (eqb l r).
  End GroupName.
  Notation GroupName := GroupName.type.

  Declare Scope GroupName_scope.
  Delimit Scope GroupName_scope with GrName.
  Infix "=?" := GroupName.eqs (at level 70): GroupName_scope.
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
    (* c *)
    | AsciiControlEsc (l: AsciiLetter)
    (* 0 *)
    | Zero
    (* x *)
    | HexEscape (d1 d2: HexDigit)
    (*+ TODO: u *)
    | IdentityEsc (chr: Character).

    Definition eqs (l r: type): {l = r} + {~ l = r}.
    Proof. decide equality; first [ apply ControlEscape.eqs | apply Character.eqs | apply AsciiLetter.eqs | apply HexDigit.eqs ]. Defined.
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
  | InputStart (*+ ^ *)
  | InputEnd (*+ $ *)
  | WordBoundary (*+ \b *)
  | NotWordBoundary (*+ \B *)
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

  Definition zip_one (focus: Regex) (ctx: RegexContextLayer) := match ctx with
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
  end.

  Fixpoint zip (focus: Regex) (ctx: RegexContext): Regex :=
    match ctx with
    | nil => focus
    | h :: t => zip (zip_one focus h) t
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
      induction ctx; intros r0 r1 Eq.
      - assumption.
      - cbn in Eq.
        specialize IHctx with (1 := Eq); destruct a; injection IHctx as ->; reflexivity.
    Qed.

    Lemma focus_bijection: forall ctx r0 r1, zip r0 ctx = zip r1 ctx <-> r0 = r1.
    Proof. intros. split; intros. - eapply focus_injection. eassumption. - subst. reflexivity. Qed.

    Inductive Down: (Regex * RegexContext) -> (Regex * RegexContext) -> Prop :=
    | Down_Disjunction_left: forall r1 r2 ctx, Down (r1, Disjunction_left r2 :: ctx) (Disjunction r1 r2, ctx)
    | Down_Disjunction_right: forall r1 r2 ctx, Down (r2, Disjunction_right r1 :: ctx) (Disjunction r1 r2, ctx)
    | Down_Quantified_inner: forall r q ctx, Down (r, Quantified_inner q :: ctx) (Quantified r q, ctx)
    | Down_Seq_left: forall r1 r2 ctx, Down (r1, Seq_left r2 :: ctx) (Seq r1 r2, ctx)
    | Down_Seq_right: forall r1 r2 ctx, Down (r2, Seq_right r1 :: ctx) (Seq r1 r2, ctx)
    | Down_Group_inner: forall name r ctx, Down (r, Group_inner name :: ctx) (Group name r, ctx)
    | Down_Lookahead_inner: forall r ctx, Down (r, Lookahead_inner :: ctx) (Lookahead r, ctx)
    | Down_NegativeLookahead_inner: forall r ctx, Down (r, NegativeLookahead_inner :: ctx) (NegativeLookahead r, ctx)
    | Down_Lookbehind_inner: forall r ctx, Down (r, Lookbehind_inner :: ctx) (Lookbehind r, ctx)
    | Down_NegativeLookbehind_inner: forall r ctx, Down (r, NegativeLookbehind_inner :: ctx) (NegativeLookbehind r, ctx).

    Notation "'Down*'" := (Relation_Operators.clos_refl_trans _ Down).

    Module Down.
      Lemma same_root: forall root r0 ctx0 r1 ctx1, Down (r0, ctx0) (r1, ctx1) -> (Root root r0 ctx0 <-> Root root r1 ctx1).
      Proof. unfold Root. intros. dependent destruction H; cbn; easy. Qed.

      Lemma same_root_down0: forall root r0 ctx0 r1 ctx1, Down (r0, ctx0) (r1, ctx1) -> Root root r1 ctx1 -> Root root r0 ctx0.
      Proof. intros. rewrite -> (same_root _ _ _ _ _ ltac:(eassumption)). assumption. Qed.

      Lemma same_root_down: forall root r0 ctx0 r1 ctx1, Down* (r0, ctx0) (r1, ctx1) -> Root root r1 ctx1 -> Root root r0 ctx0.
      Proof.
        intros root r0 ctx0 r1 ctx1 D R_root. dependent induction D.
        - eapply same_root_down0; eassumption.
        - assumption.
        - destruct y as [ ri ctxi ]. specialize IHD1 with (1 :=  eq_refl) (2 := eq_refl). specialize IHD2 with (1 :=  eq_refl) (2 := eq_refl).
          apply IHD1. apply IHD2. assumption.
      Qed.

      Lemma root_is_top: forall root ctx r, Root root r ctx -> Down* (r, ctx) (root, nil).
      Proof.
        intros root. induction ctx; intros r Root.
        - apply Root.nil in Root. subst. apply Relation_Operators.rt_refl.
        - remember (zip_one r a) as r' eqn:Eq_r'.
          assert (Down (r, a :: ctx) (r', ctx)) as D_step by (destruct a; subst; cbn in *; constructor).
          apply Relation_Operators.rt_trans with (y := (r', ctx)).
          + apply Relation_Operators.rt_step. assumption.
          + apply IHctx. rewrite <- same_root by eapply D_step. assumption.
      Qed.

      Lemma down_prefix: forall r0 ctx0 r1 ctx1, Down* (r0, ctx0) (r1, ctx1) -> exists ext, ctx0 = ext ++ ctx1.
      Proof.
        intros r0 ctx0 r1 ctx1 D. dependent induction D.
        - dependent destruction H; match goal with | [|- exists _, ?a :: ?ctx = _ ++ ?ctx ] => exists (a :: nil) end; reflexivity.
        - exists nil. reflexivity.
        - destruct y as [ ri ctxi ].
          specialize IHD1 with (1 := eq_refl) (2 := eq_refl) as [ ext0 Eq_ext0 ].
          specialize IHD2 with (1 := eq_refl) (2 := eq_refl) as [ ext1 Eq_ext1 ].
          exists (ext0 ++ ext1). subst. apply app_assoc.
      Qed.

      Lemma antisymmetry: forall n0 n1, Down* n0 n1 -> Down* n1 n0 -> n0 = n1.
      Proof.
        intros [r0 ctx0] [r1 ctx1] D01 D10.
        pose proof (down_prefix _ _ _ _ D01) as [ext01 Eq_01].
        pose proof (down_prefix _ _ _ _ D10) as [ext10 Eq_10].
        pose proof (List.mutual_prefixes _ _ _ _ Eq_01 Eq_10) as <-. clear Eq_01 Eq_10 ext01 ext10.

        remember (zip r0 ctx0) as root eqn:Eq_root.
        assert (Root root r0 ctx0) as Root_0 by (subst; reflexivity). clear Eq_root.
        pose proof (same_root_down _ _ _ _ _ D10 Root_0) as Root_1.
        unfold Root in *. rewrite -> Root_1 in Root_0.
        pose proof (focus_injection _ _ _ Root_0). subst.
        reflexivity.
      Qed.
    End Down.

    Module Walk.
      Fixpoint walk (r: Regex) (ctx: RegexContext): list (Regex * RegexContext) :=
        (r, ctx) ::
        match r with
        | Empty => nil
        | Char _ => nil
        | Dot => nil
        | CharacterClass _ => nil
        | AtomEsc _ => nil
        | Disjunction r1 r2 => walk r1 (Disjunction_left r2 :: ctx) ++ walk r2 (Disjunction_right r1 :: ctx)
        | Quantified r0 q => walk r0 (Quantified_inner q :: ctx)
        | Seq r1 r2 => walk r1 (Seq_left r2 :: ctx) ++ walk r2 (Seq_right r1 :: ctx)
        | Group name r0 => walk r0 (Group_inner name :: ctx)
        | InputStart => nil
        | InputEnd => nil
        | WordBoundary => nil
        | NotWordBoundary => nil
        | Lookahead r0 => walk r0 (Lookahead_inner :: ctx)
        | NegativeLookahead r0 => walk r0 (NegativeLookahead_inner :: ctx)
        | Lookbehind r0 => walk r0 (Lookbehind_inner :: ctx)
        | NegativeLookbehind r0 => walk r0 (NegativeLookbehind_inner :: ctx)
        end.

      Lemma shape: forall r ctx, exists t, walk r ctx = (r, ctx) :: t.
      Proof. intros. destruct r; cbn; eexists; reflexivity. Qed.

      Lemma down_yield_sublist0 {F: Type} {_: Result.AssertionError F}: forall r0 ctx0 r1 ctx1,
        Down (r0, ctx0) (r1, ctx1) -> List.Sublist.sublist (walk r0 ctx0) (walk r1 ctx1).
      Proof.
        intros r0 ctx0 r1 ctx1 D; dependent destruction D; cbn;
          repeat match goal with
          | [|- List.Sublist.sublist ?s (_ :: ?s) ] =>
              apply List.Sublist.cons_super; apply List.Sublist.refl
          | [|- List.Sublist.sublist ?s (_ :: (?s ++ ?l)) ] =>
              apply List.Sublist.trans with (l1 := (s ++ l));
                [ apply List.Sublist.concat_super_right; apply List.Sublist.refl
                | apply List.Sublist.cons_super; apply List.Sublist.refl ]
          | [|- List.Sublist.sublist ?s (_ :: (?l ++ ?s)) ] =>
              apply List.Sublist.trans with (l1 := (l ++ s));
                [ apply List.Sublist.concat_super_left; apply List.Sublist.refl
                | apply List.Sublist.cons_super; apply List.Sublist.refl ]
          end.
      Qed.

      Lemma down_yield_sublist {F: Type} {_: Result.AssertionError F}: forall r0 ctx0 r1 ctx1,
        Down* (r0, ctx0) (r1, ctx1) -> List.Sublist.sublist (walk r0 ctx0) (walk r1 ctx1).
      Proof.
        intros r0 ctx0 r1 ctx1 D. dependent induction D.
        - apply down_yield_sublist0. assumption.
        - apply List.Sublist.refl.
        - destruct y as [ri ctxi]. specialize IHD1 with (X := X) (1 := eq_refl) (2 := eq_refl). specialize IHD2 with (X := X) (1 := eq_refl) (2 := eq_refl).
          apply List.Sublist.trans with (l1 := (walk ri ctxi)); assumption.
      Qed.

      Lemma soundness {F: Type} {_: Result.AssertionError F}: forall r ctx, List.Forall.Forall (walk r ctx) (fun node => Down* node (r, ctx)).
      Proof.
        induction r; intros ctx i [ r' ctx' ] Eq_indexed; cbn in *;
          (destruct i; [ intros; cbn in *; injection Eq_indexed as <- <-; apply (Relation_Operators.rt_refl) | rewrite -> List.Indexing.Nat.cons in Eq_indexed ]).
        - rewrite -> List.Indexing.Nat.nil in Eq_indexed. Result.assertion_failed_helper.
        - rewrite -> List.Indexing.Nat.nil in Eq_indexed. Result.assertion_failed_helper.
        - rewrite -> List.Indexing.Nat.nil in Eq_indexed. Result.assertion_failed_helper.
        - rewrite -> List.Indexing.Nat.nil in Eq_indexed. Result.assertion_failed_helper.
        - rewrite -> List.Indexing.Nat.nil in Eq_indexed. Result.assertion_failed_helper.
        - apply List.Indexing.Nat.concat in Eq_indexed as  [[ _ Eq_indexed ]|[ _ Eq_indexed ]].
          + symmetry in Eq_indexed. specialize (IHr1 _ _ _ Eq_indexed). apply Relation_Operators.rt_trans with (1 := IHr1). apply Relation_Operators.rt_step. constructor.
          + symmetry in Eq_indexed. specialize (IHr2 _ _ _ Eq_indexed). apply Relation_Operators.rt_trans with (1 := IHr2). apply Relation_Operators.rt_step. constructor.
        - specialize (IHr _ _ _ Eq_indexed). apply Relation_Operators.rt_trans with (1 := IHr). apply Relation_Operators.rt_step. constructor.
        - apply List.Indexing.Nat.concat in Eq_indexed as  [[ _ Eq_indexed ]|[ _ Eq_indexed ]].
          + symmetry in Eq_indexed. specialize (IHr1 _ _ _ Eq_indexed). apply Relation_Operators.rt_trans with (1 := IHr1). apply Relation_Operators.rt_step. constructor.
          + symmetry in Eq_indexed. specialize (IHr2 _ _ _ Eq_indexed). apply Relation_Operators.rt_trans with (1 := IHr2). apply Relation_Operators.rt_step. constructor.
        - specialize (IHr _ _ _ Eq_indexed). apply Relation_Operators.rt_trans with (1 := IHr). apply Relation_Operators.rt_step. constructor.
        - rewrite -> List.Indexing.Nat.nil in Eq_indexed. Result.assertion_failed_helper.
        - rewrite -> List.Indexing.Nat.nil in Eq_indexed. Result.assertion_failed_helper.
        - rewrite -> List.Indexing.Nat.nil in Eq_indexed. Result.assertion_failed_helper.
        - rewrite -> List.Indexing.Nat.nil in Eq_indexed. Result.assertion_failed_helper.
        - specialize (IHr _ _ _ Eq_indexed). apply Relation_Operators.rt_trans with (1 := IHr). apply Relation_Operators.rt_step. constructor.
        - specialize (IHr _ _ _ Eq_indexed). apply Relation_Operators.rt_trans with (1 := IHr). apply Relation_Operators.rt_step. constructor.
        - specialize (IHr _ _ _ Eq_indexed). apply Relation_Operators.rt_trans with (1 := IHr). apply Relation_Operators.rt_step. constructor.
        - specialize (IHr _ _ _ Eq_indexed). apply Relation_Operators.rt_trans with (1 := IHr). apply Relation_Operators.rt_step. constructor.
      Qed.

      Lemma completeness {F: Type} {f: Result.AssertionError F}: forall n0 r1 ctx1, Down* n0 (r1, ctx1) -> List.Exists.ExistValue (walk r1 ctx1) n0.
      Proof.
        setoid_rewrite <- List.Exists.exist_value_eq.
        intros [r0 ctx0] r1 ctx1 D.
        pose proof down_yield_sublist as S_w. specialize S_w with (1 := D).
        apply List.Sublist.exist with (1 := S_w).
        destruct (shape r0 ctx0) as [ ? -> ].
        apply List.Exists.cons_head. reflexivity.
      Qed.

      Lemma uniqueness {F: Type} {f: Result.AssertionError F}: forall r ctx i j v,
        List.Indexing.Nat.indexing (walk r ctx) i = Success v ->
        List.Indexing.Nat.indexing (walk r ctx) j = Success v ->
        i = j.
      Proof.
        induction r; intros ctx i j v Eq_indexed_i Eq_indexed_j; cbn in *;
          repeat lazymatch goal with
          | [ H: ?x = ?x |- _ ] => clear H
          | [ H: Success _ = List.Indexing.Nat.indexing _ _ |- _ ] => symmetry in H
          | [ H: List.Indexing.Nat.indexing nil _ = Success _ |- _ ] => solve [ rewrite -> List.Indexing.Nat.nil in H; Result.assertion_failed_helper ]
          | [ H: List.Indexing.Nat.indexing (_ :: _) ?i = Success _ |- _ ] =>
              destruct i; [ cbn in H; try injection H as <- | rewrite -> List.Indexing.Nat.cons in H ]
          | [ H: List.Indexing.Nat.indexing (_ ++ _) ?i = Success _ |- _ ] =>
              apply List.Indexing.Nat.concat in H as [ [ ? H ] | [ ? H ]]
          end;
          try solve
          [ lazymatch goal with | [ H: List.Indexing.Nat.indexing (walk ?r0 ?ctx0) _ = Success ?n1 |- _ ] =>
              apply soundness in H;
              assert (Down* (r0, ctx0) n1) as Falsum by (constructor; constructor);
              apply Down.antisymmetry with (2 := H) in Falsum as [=]; List.rec_eq
              end
          | reflexivity].
        - f_equal. eapply IHr1; eassumption.
        - destruct v as [ r' ctx' ].
          apply soundness in Eq_indexed_i. apply Down.down_prefix in Eq_indexed_i as [pre_i ctx_i].
          apply soundness in Eq_indexed_j. apply Down.down_prefix in Eq_indexed_j as [pre_j ctx_j].
          rewrite -> ctx_j in ctx_i.
          apply List.same_tail in ctx_i. discriminate.
        - destruct v as [ r' ctx' ].
          apply soundness in Eq_indexed_i. apply Down.down_prefix in Eq_indexed_i as [pre_i ctx_i].
          apply soundness in Eq_indexed_j. apply Down.down_prefix in Eq_indexed_j as [pre_j ctx_j].
          rewrite -> ctx_j in ctx_i.
          apply List.same_tail in ctx_i. discriminate.
        - f_equal. apply (NNI.sub_lower _ _ _ H0 H). eapply IHr2 ; eassumption.
        - f_equal. eapply IHr; eassumption.
        - f_equal. eapply IHr1; eassumption.
        - destruct v as [ r' ctx' ].
          apply soundness in Eq_indexed_i. apply Down.down_prefix in Eq_indexed_i as [pre_i ctx_i].
          apply soundness in Eq_indexed_j. apply Down.down_prefix in Eq_indexed_j as [pre_j ctx_j].
          rewrite -> ctx_j in ctx_i.
          apply List.same_tail in ctx_i. discriminate.
        - destruct v as [ r' ctx' ].
          apply soundness in Eq_indexed_i. apply Down.down_prefix in Eq_indexed_i as [pre_i ctx_i].
          apply soundness in Eq_indexed_j. apply Down.down_prefix in Eq_indexed_j as [pre_j ctx_j].
          rewrite -> ctx_j in ctx_i.
          apply List.same_tail in ctx_i. discriminate.
        - f_equal. apply (NNI.sub_lower _ _ _ H0 H). eapply IHr2 ; eassumption.
        - f_equal. eapply IHr; eassumption.
        - f_equal. eapply IHr; eassumption.
        - f_equal. eapply IHr; eassumption.
        - f_equal. eapply IHr; eassumption.
        - f_equal. eapply IHr; eassumption.
      Qed.
    End Walk.
  End Zip.

End Patterns.
Export Patterns.
