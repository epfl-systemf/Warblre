From Coq Require Import List Program.Equality PeanoNat.
From Warblre Require Import List Result Base Patterns Node.

Import Patterns.

(**
    Lemmas and definitions on RegexNodes, i.e. regex zippers.
*)

Module Zipper.
  Module Root. Section main.
    Context `{specParameters: Parameters}.

    Lemma id: forall r, Root r (r, nil).
    Proof. intros. reflexivity. Qed.

    Lemma nil: forall r r', Root r (r', nil) -> r = r'.
    Proof. intros. unfold Root in H. cbn in H. assumption. Qed.
  End main. End Root.

  Module Zip. Section main.
    Context `{specParameters: Parameters}.

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
  End main. End Zip.

  (** 
      The down relation represents the idea that a RegexNode can be reached by going one step down in the focused
      regex.
      E.g.
        from (a|b) with context (_c)*, the two nodes
        - a with context ((_|b)c)*
        - b with context ((a|_)c)*
        are the two and only two nodes which are down w.r.t to the original node.
  *)
  Section Down.
    Context `{specParameters: Parameters}.
    Import Patterns.

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

    Definition Down_Star := (Relation_Operators.clos_refl_trans _ Down).
  End Down.
  (* Transitive reflexive closure of Down. *)
  Notation "'Down*'" := Down_Star.

  Module Down. Section main.
    Context `{specParameters: Parameters}.

    Lemma same_root: forall root r0 ctx0 r1 ctx1, Down (r0, ctx0) (r1, ctx1) -> (Root root (r0, ctx0) <-> Root root (r1, ctx1)).
    Proof. unfold Root. intros. dependent destruction H; cbn; easy. Qed.

    Lemma same_root_down0: forall root r0 ctx0 r1 ctx1, Down (r0, ctx0) (r1, ctx1) -> Root root (r1, ctx1) -> Root root (r0, ctx0).
    Proof. intros. rewrite -> (same_root _ _ _ _ _ ltac:(eassumption)). assumption. Qed.

    Lemma same_root_down: forall root r0 ctx0 r1 ctx1, Down* (r0, ctx0) (r1, ctx1) -> Root root (r1, ctx1) -> Root root (r0, ctx0).
    Proof.
      intros root r0 ctx0 r1 ctx1 D R_root. dependent induction D.
      - eapply same_root_down0; eassumption.
      - assumption.
      - destruct y as [ ri ctxi ]. specialize IHD1 with (1 :=  eq_refl) (2 := eq_refl). specialize IHD2 with (1 :=  eq_refl) (2 := eq_refl).
        apply IHD1. apply IHD2. assumption.
    Qed.

    Lemma root_is_top: forall root ctx r, Root root (r, ctx) -> Down* (r, ctx) (root, nil).
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
      assert (Root root (r0, ctx0)) as Root_0 by (subst; reflexivity). clear Eq_root.
      pose proof (same_root_down _ _ _ _ _ D10 Root_0) as Root_1.
      unfold Root in *. rewrite -> Root_1 in Root_0.
      pose proof (Zip.focus_injection _ _ _ Root_0). cbn in *. subst.
      reflexivity.
    Qed.
  End main. End Down.

  (** A walk must return a list of all sub-nodes of the provided node *)
  Module Walk. Section main.
    Context `{specParameters: Parameters}.

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

    (* First element of the walk is the node passed as argument. *)
    Lemma head: forall r ctx, exists t, walk r ctx = (r, ctx) :: t.
    Proof. intros. destruct r; cbn; eexists; reflexivity. Qed.

    (* Doing a walk on a sub-regex yield a sub-list *)
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

    (* All elements of the list are sub-nodes of the provided node *)
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

    (* All subnodes are in the list *)
    Lemma completeness {F: Type} {f: Result.AssertionError F}: forall n0 r1 ctx1, Down* n0 (r1, ctx1) -> List.Exists.ExistValue (walk r1 ctx1) n0.
    Proof.
      setoid_rewrite <- List.Exists.exist_value_eq.
      intros [r0 ctx0] r1 ctx1 D.
      pose proof down_yield_sublist as S_w. specialize S_w with (1 := D).
      apply List.Sublist.exist with (1 := S_w).
      destruct (head r0 ctx0) as [ ? -> ].
      apply List.Exists.cons_head. reflexivity.
    Qed.

    (* The returned list does not contain any duplicates *)
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
  End main. End Walk.
End Zipper.

(**
    A custom induction principle for RegexNodes.
    It is base on the previously introduced concept of sub-regex.

    In the case of a regex r, one will be able to assume that [forall r', Down r' r -> P r'].
*)
Section Induction.
    Context `{specParameters: Parameters}.
    Import Patterns.

    Lemma Node_ind: forall root (P : (Regex * RegexContext) -> Prop),
      (forall ctx, 
        Root root (Empty, ctx) -> P (Empty, ctx)) ->
      (forall ctx chr,
        Root root ((Char chr), ctx) -> P ((Char chr), ctx)) ->
      (forall ctx,
        Root root (Dot, ctx) -> P (Dot, ctx)) ->
      (forall ctx ae,
        Root root ((AtomEsc ae), ctx) -> P ((AtomEsc ae), ctx)) ->
      (forall ctx cc,
        Root root ((CharacterClass cc), ctx) -> P ((CharacterClass cc), ctx)) ->
      (forall ctx r1 r2,
        Root root (r1, Disjunction_left r2 :: ctx) -> P (r1, Disjunction_left r2 :: ctx) ->
        Root root (r2, Disjunction_right r1 :: ctx) -> P (r2, Disjunction_right r1 :: ctx) ->
        Root root (Disjunction r1 r2, ctx) -> P (Disjunction r1 r2, ctx)) ->
      (forall ctx r q,
        Root root (r, Quantified_inner q :: ctx) -> P (r, Quantified_inner q :: ctx) ->
        Root root (Quantified r q, ctx) -> P (Quantified r q, ctx)) ->
      (forall ctx r1 r2,
        Root root (r1, Seq_left r2 :: ctx) -> P (r1, Seq_left r2 :: ctx) ->
        Root root (r2, Seq_right r1 :: ctx) -> P (r2, Seq_right r1 :: ctx) ->
        Root root (Seq r1 r2, ctx) -> P (Seq r1 r2, ctx)) ->
      (forall ctx name r,
        Root root (r, Group_inner name :: ctx) -> P (r, Group_inner name :: ctx) ->
        Root root (Group name r , ctx) -> P (Group name r , ctx)) ->
      (forall ctx,
        Root root (InputStart, ctx) -> P (InputStart, ctx)) ->
      (forall ctx,
        (Root root (InputEnd, ctx) -> P (InputEnd, ctx))) ->
      (forall ctx,
        (Root root (WordBoundary, ctx) -> P (WordBoundary, ctx))) ->
      (forall ctx,
        (Root root (NotWordBoundary, ctx) -> P (NotWordBoundary, ctx))) ->
      (forall ctx r,
        Root root (r, Lookahead_inner :: ctx) -> P (r, Lookahead_inner :: ctx) ->
        Root root (Lookahead r, ctx) -> P (Lookahead r, ctx)) ->
      (forall ctx r,
        Root root (r, NegativeLookahead_inner :: ctx) -> P (r, NegativeLookahead_inner :: ctx) ->
        Root root (NegativeLookahead r, ctx) -> P (NegativeLookahead r, ctx)) ->
      (forall ctx r,
        Root root (r, Lookbehind_inner :: ctx) -> P (r, Lookbehind_inner :: ctx) ->
        Root root (Lookbehind r, ctx) -> P (Lookbehind r, ctx)) ->
      (forall ctx r,
        Root root (r, NegativeLookbehind_inner :: ctx) -> P (r, NegativeLookbehind_inner :: ctx) ->
        Root root (NegativeLookbehind r, ctx) -> P (NegativeLookbehind r, ctx)) ->
      forall r ctx, Root root (r, ctx) -> P (r, ctx).
    Proof. induction r; try eauto. Qed.
End Induction.

