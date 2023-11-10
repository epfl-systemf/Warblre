From Coq Require Import ZArith Lia List Bool.
From Warblre Require Import Tactics Focus Result.

Import Result.Notations.

Theorem pseudo_nat_ind: forall P: Z -> Prop,
          P (Z.of_nat 0) ->
          (forall n: nat, P (Z.of_nat n) -> P (Z.of_nat (S n))) ->
          (forall p: positive, P (Zneg p)) ->
          forall z: Z, P z.
Proof.
  intros P H0 Hind Hneg z. destruct z.
  - apply H0.
  - rewrite <- positive_nat_Z.
    induction (Pos.to_nat p).
    + apply H0.
    + apply Hind. apply IHn.
  - apply Hneg.
Qed.

Module List.
  Local Close Scope nat.
  Local Open Scope Z.
  Local Open Scope result_flow.

  Definition empty {T: Type} := @nil T.

  Module Indexing.

    Definition indexing {T F: Type} (ls: list T) (i: Z) {failure: Result.AssertionError F}: Result.Result T F := match i with
    | Z0 => Result.from_option_assertion (List.nth_error ls 0)
    | Zpos i => Result.from_option_assertion (List.nth_error ls (Pos.to_nat i))
    | Zneg _ => Result.assertion_failed
    end.

    Lemma of_nat {T F: Type} {failure: Result.AssertionError F}: forall (ls: list T) (i: nat), indexing ls (Z.of_nat i) = Result.from_option_assertion (List.nth_error ls i).
    Proof. intros. destruct i. - reflexivity. - cbn. rewrite -> SuccNat2Pos.id_succ. reflexivity. Qed.

    Lemma failure_bounds0: forall {T F: Type} {failure: Result.AssertionError F} (ls: list T) (i: Z), @indexing T F ls i failure = Result.assertion_failed <-> (i < 0 \/ (Z.of_nat (length ls)) <= i )%Z.
    Proof. intros T F [f] ls i. destruct i; delta indexing; cbn beta iota; split; intros.
      - destruct ls eqn:Eq.
        + cbn. lia.
        + easy.
      - destruct ls.
        + easy.
        + destruct H; [ lia | easy ].
      - destruct (List.nth_error ls (Pos.to_nat p)) eqn:Eq.
        + easy.
        + rewrite -> List.nth_error_None in Eq. lia.
      - destruct H; try lia.
        rewrite <- positive_nat_Z in H. rewrite <- Nat2Z.inj_le in H.
        rewrite <- List.nth_error_None in H. rewrite -> H.
        easy.
      - lia.
      - easy.
    Qed.

    Lemma failure_is_assertion: forall {T F: Type} {failure: Result.AssertionError F} (ls: list T) (i: Z) (f: F),
      indexing ls i = Result.Failure f -> {| Result.f := f |} = failure.
    Proof.
      intros T F [f'] ls i f. destruct i; destruct ls; cbn in *; first[ intros [=->] | intros H ]; try easy.
      - destruct (List.nth_error _ _) eqn:Eq in *.
        + discriminate.
        + cbn in *. congruence.
      - destruct (List.nth_error _ _) eqn:Eq in *.
        + discriminate.
        + cbn in *. congruence.
    Qed.

    Lemma failure_kind: forall {T F: Type} {failure: Result.AssertionError F} (ls: list T) (i: Z) (f: F),
      indexing ls i = Result.Failure f -> indexing ls i = Result.assertion_failed.
    Proof. intros T F f' ls i f H. pose proof (failure_is_assertion ls i f H) as [=]. Result.assertion_failed_helper. Qed.

    Lemma failure_bounds: forall {T F: Type} {failure: Result.AssertionError F} (ls: list T) (i: Z) (f: F), @indexing T F ls i failure = Result.Failure f -> (i < 0 \/ (Z.of_nat (length ls)) <= i )%Z.
    Proof. intros. pose proof H as H'. apply failure_is_assertion in H. rewrite <- failure_bounds0. Result.assertion_failed_helper. Qed.

    Lemma success_bounds0: forall {T F: Type} {failure: Result.AssertionError F} (ls: list T) (i: Z),
      (exists v, indexing ls i = Success v) <-> (0 <= i /\ i < (Z.of_nat (length ls)) )%Z.
    Proof. intros T F f. split.
      - intros [ v H ]. pose proof (failure_bounds0 ls i) as [ _ Falsum ].
        destruct ( (0 <=? i) && (i <? Z.of_nat (length ls)))%Z eqn:Bounds.
        + Zhelper. lia.
        + hypotheses_reflector.
          * rewrite -> Z.leb_gt in H0. specialize (Falsum (or_introl H0)). destruct f. discriminate.
          * rewrite -> Z.ltb_ge in H0. specialize (Falsum (or_intror H0)). destruct f. discriminate.
      - intros [ Leq_0_i Le_i_len ]. pose proof (failure_bounds0 ls i) as [ Falsum _ ].
        destruct i.
        + destruct ls eqn:Eq_ls; cbn in *; try lia. exists t. reflexivity.
        + destruct (indexing ls (Z.pos p)) eqn:Eq_indexed in |- *.
          * exists s. reflexivity.
          * apply failure_kind in Eq_indexed. specialize (Falsum Eq_indexed).
            destruct Falsum; lia.
        + lia.
    Qed.

    Lemma success_bounds: forall {T F: Type} {failure: Result.AssertionError F} (ls: list T) (i: Z) (v: T),
      indexing ls i = Success v -> ( 0 <= i /\ i < (Z.of_nat (length ls)) )%Z.
    Proof. intros. pose proof ((ex_intro (fun v => _ = Success v) v) H) as Bounds_i. rewrite -> Indexing.success_bounds0 in Bounds_i. assumption. Qed.

    Lemma nil: forall {T F: Type} {failure: Result.AssertionError F} (i: Z),
      indexing (nil: list T) i = Result.assertion_failed.
    Proof.
      intros; destruct i; cbn; try easy.
      destruct (Pos.to_nat p); reflexivity.
    Qed.

    Lemma nth_error_cons: forall A h (t: list A) i, nth_error (h :: t) (S i) = nth_error t i.
    Proof. induction t; intros; reflexivity. Qed.

    Lemma cons: forall {T F: Type} {failure: Result.AssertionError F} (h: T) (t: list T) (i: Z),
      0 <= i -> indexing (h :: t) (i + 1) = indexing t i.
    Proof.
      intros; destruct t; destruct (i + 1) eqn:Eq_Si; try lia.
      - cbn. destruct (Pos.to_nat p) eqn:Eq_p; try lia. cbn. rewrite -> nil. destruct n; reflexivity.
      - cbn. pose proof (Pos2Nat.is_succ p) as [i' Eq_i']. rewrite -> Eq_i'.
        assert (i = Z.of_nat i') as Eq_ii' by lia.
        rewrite -> Eq_ii' in *. subst. clear Eq_i'. clear Eq_Si. clear p.
        rename i' into i.
        destruct i eqn:Eq_i.
        + reflexivity.
        + cbn. rewrite -> SuccNat2Pos.id_succ. rewrite -> nth_error_cons. reflexivity.
    Qed.
  End Indexing.

  Module Updating.
    Fixpoint updating_nat {T F: Type} (ls: list T) (i: nat) (v: T) {failure: Result.AssertionError F}: Result.Result (list T) F := match ls with
    | nil => Result.assertion_failed
    | h :: t =>  match i with
      | 0%nat => Success (v :: t)
      | S i' => let! t' =<< updating_nat t i' v in Success (h :: t')
      end
    end.

    Definition updating {T F: Type} (ls: list T) (i: Z) (v: T) {failure: Result.AssertionError F}: Result.Result (list T) F := match i with
    | Z0 => updating_nat ls 0 v
    | Zpos i => updating_nat ls (Pos.to_nat i) v
    | Zneg _ => Result.assertion_failed
    end.

    Lemma failure_bounds_nat: forall {T F: Type} {failure: Result.AssertionError F} (ls: list T) (i: nat) (v: T), @updating_nat T F ls i v failure = Result.assertion_failed <-> (length ls <= i )%nat.
    Proof. 
      intros T F failure.
      induction ls; intros.
      - split; cbn; [ lia | easy ].
      - split; cbn.
        + focus § _ [] _ -> _ § auto destruct; Result.assertion_failed_helper.
          intros [=->]. rewrite -> IHls in AutoDest_0. lia.
        + intros. focus § _ [] _ § auto destruct.
          * lia.
          * destruct (IHls n v) as [ _ IHls' ].
            rewrite -> IHls' in AutoDest_0 by lia.
            Result.assertion_failed_helper.
          * rewrite <- AutoDest_0. rewrite -> IHls. lia.
    Qed.

    Lemma failure_is_assertion_nat: forall {T F: Type} {failure: Result.AssertionError F} (ls: list T) (i: nat) (f: F) (v: T),
      updating_nat ls i v = Result.Failure f -> {| Result.f := f |} = failure.
    Proof.
      induction ls; intros i f v; destruct i; cbn in *; Result.assertion_failed_helper; first[ intros [=->] | intros H ]; try easy.
      destruct (updating_nat ls i v) eqn:Eq.
      - discriminate.
      - clean_injection H. specialize IHls with (1 := Eq). subst. Result.assertion_failed_helper.
    Qed.

    Lemma failure_kind_nat: forall {T F: Type} {failure: Result.AssertionError F} (ls: list T) (i: nat) (f: F) (v: T),
      updating_nat ls i v = Result.Failure f -> updating_nat ls i v = Result.assertion_failed.
    Proof. intros. pose proof (failure_is_assertion_nat ls i f v H). Result.assertion_failed_helper. Qed.

    Lemma failure_bounds: forall {T F: Type} {failure: Result.AssertionError F} (ls: list T) (i: Z) (v: T), @updating T F ls i v failure = Result.assertion_failed <-> (i < 0 \/ Z.of_nat (length ls) <= i )%Z.
    Proof.
      intros. split.
      - intros. destruct i; cbn in H.
        + apply failure_bounds_nat in H. right. lia.
        + apply failure_bounds_nat in H. right. lia.
        + left. lia.
      - intros [ i_leq_0 | len_le_i ]; destruct i; cbn.
        + lia.
        + lia.
        + reflexivity.
        + destruct ls; cbn in *; try lia. reflexivity.
        + apply failure_bounds_nat. lia.
        + lia.
    Qed.

    Lemma failure_is_assertion: forall {T F: Type} {failure: Result.AssertionError F} (ls: list T) (i: Z) (f: F) (v: T),
      updating ls i v = Result.Failure f -> {| Result.f := f |} = failure.
    Proof.
      intros. destruct i.
      - apply failure_is_assertion_nat in H. assumption.
      - apply failure_is_assertion_nat in H. assumption.
      - cbn in H. Result.assertion_failed_helper.
    Qed.

    Lemma failure_kind: forall {T F: Type} {failure: Result.AssertionError F} (ls: list T) (i: Z) (f: F) (v: T),
      updating ls i v = Result.Failure f -> updating ls i v = Result.assertion_failed.
    Proof. intros. pose proof (failure_is_assertion ls i f v H). Result.assertion_failed_helper. Qed.

    Lemma success_bounds: forall {T F: Type} {failure: Result.AssertionError F} (ls: list T) (i: Z) (v: T),
      (exists ls', updating ls i v = Success ls') <-> (0 <= i /\ i < (Z.of_nat (length ls)) )%Z.
    Proof. intros T F f. split.
      - intros [ ls' H ]. pose proof (failure_bounds ls i) as [ _ Falsum ].
        destruct ( (0 <=? i) && (i <? Z.of_nat (length ls)))%Z eqn:Bounds.
        + Zhelper. lia.
        + hypotheses_reflector.
          * rewrite -> Z.leb_gt in H0. specialize (Falsum (or_introl H0)). destruct f. discriminate.
          * rewrite -> Z.ltb_ge in H0. specialize (Falsum (or_intror H0)). destruct f. discriminate.
      - intros [ Leq_0_i Le_i_len ]. pose proof (failure_bounds ls i v) as [ Falsum _ ].
        destruct i eqn:Eq_i.
        + destruct ls eqn:Eq_ls; cbn in *; try lia. exists (v :: l). reflexivity.
        + destruct (updating ls (Z.pos p) v) eqn:Eq_indexed in |- *.
          * exists s. reflexivity.
          * apply failure_kind in Eq_indexed. specialize (Falsum Eq_indexed).
            destruct Falsum; lia.
        + lia.
    Qed.
  End Updating.

  Module Exists.
    Fixpoint exist {T F: Type} (ls: list T) (p: T -> Result bool F): Result bool F := match ls with
    | nil => Success false
    | h :: t => let! b: bool =<< p h in if b then Success true else exist t p
    end.
  End Exists.

  Module Range.
    Module Impl.
      Fixpoint range (base: Z) (l: nat) := match l with
      | 0%nat => nil
      | S l' => base :: (range (base + 1) l')
      end.

      Lemma length: forall l b, length (range b l) = l.
      Proof. induction l; intros b; cbn. - reflexivity. - rewrite -> IHl. reflexivity. Qed.

      Lemma indexing {F: Type} {f: Result.AssertionError F}: forall i b l v,
        Indexing.indexing (range b l) i = Success v -> v = (b + i).
      Proof.
        induction i using pseudo_nat_ind.
        - intros. cbn in *.
          destruct l; try Result.assertion_failed_helper. cbn in *.
          injection H as [=->]. lia.
        - intros. cbn in *. rewrite -> SuccNat2Pos.id_succ in H.
          destruct l; try Result.assertion_failed_helper. cbn in *.
          specialize (IHi (b + 1) l). cbn in IHi.
          rewrite -> Indexing.of_nat in *. specialize (IHi _ H).
          lia.
        - intros. cbn in H. Result.assertion_failed_helper.
      Qed.
    End Impl.

    Definition IsRange (from to: Z) (ls: list Z) :=
      (forall (F: Type) (f: Result.AssertionError F) z, from <= z < to -> Indexing.indexing ls (z - from) = Success z).

    Definition range(from to: Z) := Impl.range from (Z.to_nat (to - from)).

    Lemma length: forall s e, length (range s e) = Z.to_nat (e - s).
    Proof. unfold range. intros. apply Impl.length. Qed.

    Lemma indexing {F: Type} {f: Result.AssertionError F}: forall s e i v,
      Indexing.indexing (range s e) i = Success v -> v = (s + i).
    Proof. unfold range. intros. apply Impl.indexing with (1 := H). Qed.

    Lemma completeness {F: Type} {f: Result.AssertionError F}: forall s e z, s <= z -> z < e -> exists i, Indexing.indexing (range s e) i = Success z.
    Proof.
      intros. remember (z - s) as i.
      exists i.
      assert (0 <= i < Z.of_nat (Z.to_nat (e - s))) as Bounds_z by lia.
      rewrite <- length in Bounds_z.
      destruct (Indexing.indexing (range s e) i) eqn:Eq.
      - apply indexing in Eq. f_equal. lia.
      - apply Indexing.failure_bounds in Eq. lia.
    Qed.

    Lemma range_sortedness {F: Type} {f: Result.AssertionError F}: forall s e i0 i1 z0 z1,
      (i0 <= i1)%Z ->
      Indexing.indexing (range s e) i0 = Success z0 ->
      Indexing.indexing (range s e) i1 = Success z1 ->
      (z0 <= z1)%Z.
    Proof. intros. apply indexing in H0. apply indexing in H1. lia. Qed.
  End Range.
End List.