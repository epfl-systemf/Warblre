From Coq Require Import Program.Tactics Bool.Bool ZArith.

Tactic Notation "delta" reference(id) := cbv delta [ id ].
Tactic Notation "delta" reference(id) "in" hyp(h) := cbv delta [ id ] in h.
Tactic Notation "deltaf" constr(id) := cbv delta [ id ]; cbn fix; fold id.
Tactic Notation "deltaf" constr(id) "in" hyp(h) := delta id in h; cbn fix in h; fold id in h.

Ltac is_compound t := match t with
  | ?l => is_constructor l
  | ?l _ => is_compound l
end.

Ltac not_in_context Z :=
  match goal with
  | [ _ : Z |- _ ] => fail 1
  | [ |- _ ] => idtac
  end.

Ltac squeeze H := inversion H; clear H; subst.

Ltac exApplyW_internal H w As := lazymatch type of H with
  | ex ?P -> ?Q =>  let H' := fresh in 
                    assert (H': ex P); [ exists w; assumption | ];
                    pose proof (H H') as As;
                    clear H'
  | ?T => fail H " does not have the expected type. Expected: (ex ?P -> ?Q). Got: " T
  end.
Tactic Notation "exApplyW" hyp(H) hyp(w) :=
  let As := fresh in
  exApplyW_internal H w As.
Tactic Notation "exApplyW" hyp(H) hyp(w) "as" simple_intropattern(As) :=
  exApplyW_internal H w As.

Ltac clean_injection H := injection H; clear H; intros.

Ltac bookkeeper := repeat (
      Coq.Program.Tactics.destruct_conjs 
  ||  Coq.Program.Tactics.clear_dups 
  ||  subst
  ||  lazymatch goal with
      | [ H: _ = _ |- _ ] => clean_injection H || discriminate H
      end).

Module Decidability.
  Lemma dec_dneg: forall P, {P}+{~P} -> ~~P -> P.
  Proof. 
    intros Pr [ P | nP ] nnP.
    - assumption.
    - exfalso. apply nnP. apply nP.
  Qed.

  Lemma dec_reflect : forall P, {P}+{~P} -> (Bool.reflect P true + Bool.reflect P false).
  Proof. 
    intros Pr [ P | nP ].
    - left. apply Bool.ReflectT. assumption.
    - right. apply Bool.ReflectF. assumption.
  Qed.
End Decidability.

Module ZExtra.

  Lemma geb_leb_iff: forall x y b, Z.geb x y = b <-> Z.leb y x = b.
  Proof. intros. unfold Z.geb. unfold Z.leb. destruct (Z.compare x y) eqn:Eq.
    - apply Z.compare_eq in Eq. subst. rewrite -> Z.compare_refl. split; intros; assumption.
    - rewrite <- Zcompare_Gt_Lt_antisym in Eq. rewrite -> Eq. split; intros; assumption.
    - rewrite -> Zcompare_Gt_Lt_antisym in Eq. rewrite -> Eq. split; intros; assumption.
  Qed.

  Lemma gtb_ltb_iff: forall x y b, Z.gtb x y = b <-> Z.ltb y x = b.
  Proof. intros. unfold Z.gtb. unfold Z.ltb. destruct (Z.compare x y) eqn:Eq.
    - apply Z.compare_eq in Eq. subst. rewrite -> Z.compare_refl. split; intros; assumption.
    - rewrite <- Zcompare_Gt_Lt_antisym in Eq. rewrite -> Eq. split; intros; assumption.
    - rewrite -> Zcompare_Gt_Lt_antisym in Eq. rewrite -> Eq. split; intros; assumption.
  Qed.
End ZExtra.
Ltac normalize_Z_comp := repeat
(   rewrite -> Z.ge_le_iff in *
||  rewrite -> ZExtra.geb_leb_iff in *
||  rewrite -> ZExtra.gtb_ltb_iff in * ).


Module Reflection.
  Ltac apply_to_iff H a := let lr := fresh in let rl := fresh in let G := fresh "H" in
    pose proof H as G; destruct G as [ lr rl ];
    first [pose proof (lr a) as G | pose proof (rl a) as G];
    clear lr; clear rl.

  Lemma reflect_iff_false : forall P b, Bool.reflect P b -> (~P<->b=false).
  Proof. intros P b H. split.
    - intros nP. destruct b.
      + squeeze H. exfalso. apply nP. assumption.
      + reflexivity.
    - intros E. subst. squeeze H. assumption.
  Qed.
End Reflection.

Ltac fforward := repeat match goal with
| [ H0: ?P -> ?Q, H1: ?P |- _ ] => specialize (H0 H1)
| [ H0: (?x = ?x) -> ?Q |- _ ] => specialize (H0 (eq_refl x))
end.

Ltac destruct_match := simpl in *; match goal with
  | [ H: context[ match ?c with | _ => _ end ] |- _ ] => let E := fresh "E" in destruct c eqn:E
  | [ |- context[ match ?c with | _ => _ end ] ] => let E := fresh "E" in destruct c eqn:E
  | [ H: context[ if ?c then _ else _ ] |- _ ] => let E := fresh "E" in destruct c eqn:E
  | [ |- context[ if ?c then _ else _ ] ] => let E := fresh "E" in destruct c eqn:E
  end.

Ltac check_type t T := lazymatch type of t with
| T => idtac
| _ => fail
end.

Module BooleanSimplifier.
  Lemma identity_if: forall (b: bool), (if b then true else false) = b.
  Proof. intros [ ]; reflexivity. Qed.

  Lemma negating_if: forall (b: bool), (if b then false else true) = negb b.
  Proof. intros [ ]; reflexivity. Qed.
End BooleanSimplifier.

Ltac boolean_simplifier := repeat
(   rewrite -> andb_true_l in *
||  rewrite -> BooleanSimplifier.identity_if in *
||  rewrite -> BooleanSimplifier.negating_if in *
||  match goal with
    | [ H: ?c1 = ?c2 |- _ ] => check_type c1 bool; is_constructor c1; is_constructor c2; try discriminate H; clear H
    | [ H: andb _ _ = true |- _ ] => rewrite -> andb_true_iff in H; destruct H
    | [ H: orb _ _ = false |- _ ] => rewrite -> orb_false_iff in H; destruct H
    | [ H: ?b = _ |- _ ] => check_type b bool; is_constructor b; symmetry in H
    | [ H: _ = ?b |- _ ] => check_type b bool; rewrite -> H in *
    | [ H: negb _ = _ |- _ ] => apply (f_equal negb) in H; rewrite -> negb_involutive in H; cbn in H
    end).

Ltac hypotheses_reflector := repeat 
(   boolean_simplifier
||  match goal with
    | [ H: andb ?l ?r = false |- _ ] => Reflection.apply_to_iff (Bool.andb_false_iff l r) H; clear H
    | [ H: _ /\ _ |- _ ] => destruct H
    (* | [ H: _ \/ _ |- _ ] => destruct H *)
    end).

Ltac goal_reflector := repeat match goal with
  | [ |- _ && _ = true ] => apply andb_true_intro; split
  end.

Ltac introduce H := let H' := fresh H in pose proof H as H'.

Ltac reflector_base_0 spec := progress repeat (
      rewrite <- (Bool.reflect_iff _ _ spec) in *
  ||  rewrite <- (Reflection.reflect_iff_false _ _ spec) in * ).

  Ltac reflector_base_1 spec := progress repeat (
      rewrite <- (Bool.reflect_iff _ _ (spec _)) in *
  ||  rewrite <- (Reflection.reflect_iff_false _ _ (spec _)) in * ).

Ltac reflector_base_2 spec := progress repeat (
      rewrite <- (Bool.reflect_iff _ _ (spec _ _)) in *
  ||  rewrite <- (Reflection.reflect_iff_false _ _ (spec _ _)) in * ).

Ltac spec_reflector spec :=
  first [ reflector_base_0 spec
        | reflector_base_1 spec
        | reflector_base_2 spec ].


Ltac denoter_base_0 spec := progress repeat (
      rewrite -> (Bool.reflect_iff _ _ spec) in *
  ||  rewrite -> (Reflection.reflect_iff_false _ _ spec) in * ).

  Ltac denoter_base_1 spec := progress repeat (
      rewrite -> (Bool.reflect_iff _ _ (spec _)) in *
  ||  rewrite -> (Reflection.reflect_iff_false _ _ (spec _)) in * ).

Ltac denoter_base_2 spec := progress repeat (
      rewrite -> (Bool.reflect_iff _ _ (spec _ _)) in *
  ||  rewrite -> (Reflection.reflect_iff_false _ _ (spec _ _)) in * ).

Ltac spec_denoter spec :=
  first [ denoter_base_0 spec
        | denoter_base_1 spec
        | denoter_base_2 spec ].

(* Lift all computational boolean operators and Z comparisons into Props *)
Ltac Zhelper := repeat
(   hypotheses_reflector
||  goal_reflector
||  normalize_Z_comp
||  spec_reflector Z.leb_spec0
||  spec_reflector Z.ltb_spec0).

Ltac check_not_duplicated H :=
  let T := type of H in
  lazymatch goal with
  | [ _: T, _: T |- _ ] => fail
  | [ |- _ ] => idtac
  end.

Ltac split_conjs := repeat match goal with
  | [|- _ /\ _ ] => split
  end.