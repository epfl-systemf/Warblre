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

  Module FoldResult.
    Fixpoint fold_left_result0 {S T F: Type} (r: T -> S -> Result T F) (ls: list S) (racc: Result T F): Result T F := match ls with
      | nil => racc
      | s :: ls' => let! acc =<< racc in fold_left_result0 r ls' (r acc s)
      end.

    Definition fold_left_result {S T F: Type} (r: T -> S -> Result T F) (ls: list S) (zero: T): Result T F :=
      fold_left_result0 r ls (Success zero).

    Lemma zero_failure0 {S T F: Type}: forall (r: T -> S -> Result T F) (ls: list S) (f: F), fold_left_result0 r ls (Failure f) = (Failure f).
    Proof. intros r ls f. destruct ls; reflexivity. Qed.

    Lemma cons0 {S T F: Type}: forall (r: T -> S -> Result T F) (h: S) (t: list S) (zero: Result T F),
      fold_left_result0 r (h :: t) zero = let! zero' =<< zero in fold_left_result0 r t (r zero' h).
    Proof. intros r h t zero. reflexivity. Qed.

    Lemma cons {S T F: Type}: forall (r: T -> S -> Result T F) (h: S) (t: list S) (acc: T),
      fold_left_result r (h :: t) acc = let! acc' =<< r acc h in fold_left_result r t acc'.
    Proof. intros r h t acc. destruct t. - cbn; destruct (r acc h); reflexivity. - cbn. reflexivity. Qed.
  End FoldResult.

  Local Notation "'Zextend' f" := (fun ls i => match i with
    | Z0 => f ls 0%nat
    | Zpos i => f ls (Pos.to_nat i)
    | Zneg _ => Result.assertion_failed
    end) (at level 0, only parsing).

  Local Notation "'Lextend' f" := (fun ls is => List.FoldResult.fold_left_result0 f is (Success ls)) (at level 0, only parsing).

  Module Indexing.
    Module Nat.
      Definition indexing {T F: Type} {failure: Result.AssertionError F} (ls: list T) (i: nat): Result.Result T F :=
        Result.from_option_assertion (List.nth_error ls i).

      Lemma success_bounds0 {T F: Type} {_: Result.AssertionError F}: forall (ls: list T) (i: nat),
        (exists v, indexing ls i = Success v) <-> (i < length ls)%nat.
      Proof.
        unfold indexing.
        induction ls; intros i.
        - split; intros H.
          + destruct H as [ v H ]. destruct i; Result.assertion_failed_helper.
          + cbn in H. lia.
        - destruct i; cbn.
          + split. * lia. * intros _. exists a. reflexivity.
          + assert (S i < S (length ls) <-> i < (length ls))%nat as -> by lia.
            apply IHls.
      Qed.
      Lemma success_bounds {T F: Type} {_: Result.AssertionError F}: forall (ls: list T) (i: nat) (v: T),
        indexing ls i = Success v -> (i < length ls)%nat.
      Proof. intros. pose proof ((ex_intro (fun v => _ = Success v) v) H) as Bounds_i. rewrite -> success_bounds0 in Bounds_i. assumption. Qed.

      Lemma failure_is_assertion {T F: Type} {f: Result.AssertionError F}: forall (ls: list T) (i: nat) (f': F),
        indexing ls i = Result.Failure f' -> {| Result.f := f' |} = f.
      Proof.
        intros ls i f' Eq_indexed. unfold indexing in *. 
        destruct (List.nth_error _ _) in *; try discriminate.
        cbn in Eq_indexed. Result.assertion_failed_helper.
      Qed.

      Lemma failure_kind {T F: Type} {_: Result.AssertionError F}: forall (ls: list T) (i: nat) (f: F),
        indexing ls i = Result.Failure f -> indexing ls i = Result.assertion_failed.
      Proof. intros ls i f H. pose proof (failure_is_assertion ls i f H) as [=]. Result.assertion_failed_helper. Qed.

      Lemma failure_bounds0 {T F: Type} {f: Result.AssertionError F}: forall (ls: list T) (i: nat), @indexing T F f ls i = Result.assertion_failed <-> (length ls <= i )%nat.
      Proof.
        destruct f as [f]. intros ls i. rewrite <- nth_error_None.
        unfold indexing.
        destruct (nth_error ls i) eqn:Eq; cbn in *.
        - split; discriminate.
        - split; reflexivity.
      Qed.
      Lemma failure_bounds {T F: Type} {f: Result.AssertionError F}: forall (ls: list T) (i: nat) (f': F), @indexing T F f ls i = Result.Failure f' -> (length ls <= i )%nat.
      Proof. intros. pose proof H as H'. apply failure_is_assertion in H. rewrite <- failure_bounds0. Result.assertion_failed_helper. Qed.

      Lemma nil {T F: Type} {_: Result.AssertionError F}: forall (i: nat),
        indexing (nil: list T) i = Result.assertion_failed.
      Proof.
        intros; destruct i; cbn; try easy.
      Qed.

      Lemma cons {T F: Type} {_: Result.AssertionError F}: forall (h: T) (t: list T) (i: nat),
        indexing (h :: t) (S i) = indexing t i.
      Proof.
        intros h t i. destruct i.
        - reflexivity.
        - destruct t.
          + reflexivity.
          + unfold indexing. cbn. reflexivity.
      Qed.

      Lemma repeat {T F: Type} {failure: Result.AssertionError F}: forall n v i v',
        indexing (@List.repeat T v n) i = Success v' -> v = v'.
      Proof.
        intros n.
        induction n.
        - intros v i v' H. cbn in H. rewrite -> nil in H. Result.assertion_failed_helper.
        - intros v i v' H. induction i.
          + injection H as ->. reflexivity.
          + simpl repeat in H. rewrite -> cons in H.
            specialize IHn with (1 := H). assumption.
      Qed.
    End Nat.

    Module Int.
      Definition indexing {T F: Type} {_: Result.AssertionError F}: list T -> Z -> Result.Result T F := Zextend Nat.indexing.

      Lemma success_bounds0 {T F: Type} {_: Result.AssertionError F}: forall (ls: list T) (i: Z),
        (exists v, indexing ls i = Success v) <-> (0 <= i /\ i < Z.of_nat (length ls))%Z.
      Proof.
        unfold indexing. intros ls i. destruct i.
        - assert ((0 <= 0 < Z.of_nat (length ls))%Z <-> (0 < length ls)%nat) as -> by lia. apply Nat.success_bounds0.
        - assert ((0 <= Z.pos p < Z.of_nat (length ls))%Z <-> (Pos.to_nat p < length ls)%nat) as -> by lia. apply Nat.success_bounds0.
        - split. + intros [ v Falsum ]. Result.assertion_failed_helper. + lia.
      Qed.
      Lemma success_bounds {T F: Type} {_: Result.AssertionError F}: forall (ls: list T) (i: Z) (v: T),
        indexing ls i = Success v -> (0 <= i /\ i < Z.of_nat (length ls))%Z.
      Proof. intros. pose proof ((ex_intro (fun v => _ = Success v) v) H) as Bounds_i. rewrite -> success_bounds0 in Bounds_i. assumption. Qed.

      Lemma failure_is_assertion {T F: Type} {f: Result.AssertionError F}: forall (ls: list T) (i: Z) (f': F),
          indexing ls i = Result.Failure f' -> {| Result.f := f' |} = f.
      Proof.
        unfold indexing. intros ls i f' Eq_indexed. destruct i.
        - apply Nat.failure_is_assertion in Eq_indexed. assumption.
        - apply Nat.failure_is_assertion in Eq_indexed. assumption.
        - Result.assertion_failed_helper.
      Qed.

      Lemma failure_kind {T F: Type} {_: Result.AssertionError F}: forall (ls: list T) (i: Z) (f: F),
        indexing ls i = Result.Failure f -> indexing ls i = Result.assertion_failed.
      Proof. intros ls i f H. pose proof (failure_is_assertion ls i f H) as [=]. Result.assertion_failed_helper. Qed.

      Lemma failure_bounds0 {T F: Type} {f: Result.AssertionError F}: forall (ls: list T) (i: Z), @indexing T F f ls i = Result.assertion_failed <-> (i < 0 \/ (Z.of_nat (length ls)) <= i )%Z.
      Proof.
        unfold indexing. intros ls i. destruct i.
        - rewrite -> Nat.failure_bounds0. lia.
        - rewrite -> Nat.failure_bounds0. lia.
        - cbn. split. + lia. + reflexivity.
      Qed.

      Lemma failure_bounds {T F: Type} {f: Result.AssertionError F}: forall (ls: list T) (i: Z) (f': F), @indexing T F f ls i = Result.Failure f' -> (i < 0 \/ (Z.of_nat (length ls)) <= i )%Z.
      Proof. intros. pose proof H as H'. apply failure_is_assertion in H. rewrite <- failure_bounds0. Result.assertion_failed_helper. Qed.

      Lemma nil: forall {T F: Type} {f: Result.AssertionError F} (i: Z),
        indexing (nil: list T) i = Result.assertion_failed.
      Proof.
        intros; destruct i; cbn; try easy.
        destruct (Pos.to_nat p); reflexivity.
      Qed.

      Lemma cons {T F: Type} {_: Result.AssertionError F}: forall (h: T) (t: list T) (i: Z),
        (0 <= i) -> indexing (h :: t) (i + 1) = indexing t i.
      Proof.
        unfold indexing.
        intros h t i Ineq_0_i. destruct i; cbn.
        - apply Nat.cons.
        - assert (Pos.to_nat (p + 1) = S (Pos.to_nat p)) as -> by lia. apply Nat.cons.
        - lia.
      Qed.
      
      Lemma repeat {T F: Type} {failure: Result.AssertionError F}: forall n v i v',
        indexing (@List.repeat T v n) i = Success v' -> v = v'.
      Proof. intros n v i v' H. destruct i. - apply Nat.repeat with (1 := H). - apply Nat.repeat with (1 := H). - apply Indexing.Int.success_bounds in H. lia. Qed.
      
      (** Int only theorems *)

      Lemma of_nat {T F: Type} {failure: Result.AssertionError F}: forall (ls: list T) (i: nat), indexing ls (Z.of_nat i) = Nat.indexing ls i.
      Proof. intros. destruct i. - reflexivity. - cbn. rewrite -> SuccNat2Pos.id_succ. reflexivity. Qed.

      Lemma to_nat {T F: Type} {failure: Result.AssertionError F}: forall (ls: list T) (i: Z), (0 <= i)%Z -> indexing ls i = Nat.indexing ls (Z.to_nat i).
      Proof. intros. destruct i. - reflexivity. - reflexivity. - lia. Qed.

      Lemma cons_of_nat {T F: Type} {_: Result.AssertionError F}: forall (h: T) (t: list T) (i: nat) (v: T),
        indexing (h :: t) (Z.of_nat (S i)) = Success v <-> indexing t (Z.of_nat i) = Success v.
      Proof.
        intros. assert (Z.of_nat (S i) = Z.of_nat i + 1) as -> by lia.
        split; intros H.
        - rewrite -> cons in H by lia. assumption.
        - rewrite -> cons by lia. assumption.
      Qed.
    End Int.
  End Indexing.

  Module Forall.
    Definition Forall {T F: Type} {_: Result.AssertionError F} (ls: list T) (P: T -> Prop) := (forall i v, Indexing.Nat.indexing ls i = Success v -> P v).

    Lemma nil {T F: Type} {_: Result.AssertionError F}: forall (P: T -> Prop), Forall nil P.
    Proof. intros P i v H. apply Indexing.Nat.success_bounds in H. cbn in H. lia. Qed.

    Lemma cons {T F: Type} {_: Result.AssertionError F}: forall (h: T) (t: list T) (P: T -> Prop), P h -> Forall t P -> Forall (h :: t) P.
    Proof.
      intros h t P Hh Ht i v Eq_indexed. destruct i.
      - injection Eq_indexed as <-. assumption.
      - rewrite -> Indexing.Nat.cons in Eq_indexed. apply (Ht i v Eq_indexed).
    Qed.

    Lemma cons_inv_head {T F: Type} {_: Result.AssertionError F}: forall (h: T) (t: list T) (P: T -> Prop), Forall (h :: t) P -> P h.
    Proof. intros h t P F_h_t. specialize (F_h_t 0%nat h). cbn in *. fforward. assumption. Qed.

    Lemma cons_inv_tail {T F: Type} {_: Result.AssertionError F}: forall (h: T) (t: list T) (P: T -> Prop), Forall (h :: t) P -> Forall t P.
    Proof. intros h t P F_h_t i v Eq_indexed. specialize (F_h_t (S i) v). apply F_h_t. rewrite -> Indexing.Nat.cons. assumption. Qed.

    Lemma cons_inv {T F: Type} {_: Result.AssertionError F}: forall (h: T) (t: list T) (P: T -> Prop), Forall (h :: t) P -> P h /\ Forall t P.
    Proof. intros h t P F_h_t. split. - eapply cons_inv_head; eassumption. - eapply cons_inv_tail; eassumption. Qed.

    Lemma concat {T F: Type} {_: Result.AssertionError F}: forall (ls ls': list T) (P: T -> Prop), Forall ls P -> Forall ls' P -> Forall (ls ++ ls') P.
    Proof.
      induction ls; intros ls' P F_ls F_ls'; cbn.
      - assumption.
      - apply cons_inv in F_ls as [ P_a F_ls ]. intros [ | i ] v Eq_indexed.
        + cbn in Eq_indexed. injection Eq_indexed as <-. assumption.
        + rewrite -> Indexing.Nat.cons in Eq_indexed. specialize IHls with (1 := F_ls) (2 := F_ls'). specialize (IHls _ _ Eq_indexed). assumption.
    Qed.

    Lemma repeat {T F: Type} {_: Result.AssertionError F}: forall (n: nat) (t: T) (P: T -> Prop), P t -> Forall (List.repeat t n) P.
    Proof. intros n t P H i v Eq_indexed. apply Indexing.Nat.repeat in Eq_indexed. subst. assumption. Qed.

    Lemma to_Z {T F: Type} {_: Result.AssertionError F}: forall (ls: list T) (P: T -> Prop), Forall ls P -> forall i v, Indexing.Int.indexing ls i = Success v -> P v.
    Proof.
      intros ls P H [ | z | z ] v Eq_indexed.
      - rewrite -> Indexing.Int.to_nat in Eq_indexed by lia.
        cbn in Eq_indexed.
        apply (H _ _ Eq_indexed).
      - rewrite -> Indexing.Int.to_nat in Eq_indexed by lia.
        cbn in Eq_indexed.
        apply (H _ _ Eq_indexed).
      - apply Indexing.Int.success_bounds in Eq_indexed. lia.
    Qed.
  End Forall.

  Module Update.
    Module Nat.
      Module One.
        Fixpoint update {T F: Type} {_: Result.AssertionError F} (v: T) (ls: list T) (i: nat): Result.Result (list T) F := match ls with
          | nil => Result.assertion_failed
          | h :: t =>  match i with
            | 0%nat => Success (v :: t)
            | S i' => let! t' =<< update v t i' in Success (h :: t')
            end
          end.

        Lemma cons_inv_tail {T F: Type} {_: Result.AssertionError F}: forall (h: T) (t: list T) (i: nat) (v: T),
          update v (h :: t) (S i) = (let! t' =<< update v t i in Success (h :: t')).
        Proof. intros h t i v. cbn. destruct (update v t i); reflexivity. Qed.

        Lemma failure_is_assertion {T F: Type} {f: Result.AssertionError F}: forall (ls: list T) (i: nat) (v: T) (f': F),
          update v ls i = Result.Failure f' -> {| Result.f := f' |} = f.
        Proof.
          induction ls; intros i v f'.
          - cbn. Result.assertion_failed_helper. intros [=<-]. reflexivity.
          - destruct i.
            + discriminate.
            + intros H. cbn in H. destruct (update v ls i) eqn:Eq_update; try discriminate.
              injection H as <-. apply IHls with (i := i) (v := v). assumption.
        Qed.

        Lemma failure_kind {T F: Type} {_: Result.AssertionError F}: forall (ls: list T) (i: nat) (v: T) (f: F),
          update v ls i = Result.Failure f -> update v ls i = Result.assertion_failed.
        Proof. intros ls i v f H. pose proof (failure_is_assertion ls i v f H) as [=]. Result.assertion_failed_helper. Qed.

        Lemma failure_bounds0 {T F: Type} {f: Result.AssertionError F}: forall (ls: list T) (i: nat) (v: T),
          @update T F f v ls i = Result.assertion_failed <-> (length ls <= i)%nat.
        Proof.
        Admitted.

        Lemma failure_bounds {T F: Type} {f: Result.AssertionError F}: forall (ls: list T) (i: nat) (v: T) (f': F),
          @update T F f v ls i = Result.Failure f' -> (length ls <= i)%nat.
        Proof. intros. pose proof H as H'. apply failure_is_assertion in H. rewrite <- failure_bounds0 with (v := v). Result.assertion_failed_helper. Qed.

        Lemma success_length {T F: Type} {_: Result.AssertionError F}: forall (ls ls': list T) (i: nat) (v: T),
          update v ls i = Success ls' -> (length ls) = (length ls').
        Proof.
          intros ls. induction ls; intros ls' i v H.
          - Result.assertion_failed_helper.
          - destruct i.
            + injection H as <-. reflexivity.
            + cbn in *. destruct (update v ls i) eqn:Eq_updated; try discriminate.
              injection H as <-. cbn. f_equal.
              apply IHls with (1 := Eq_updated).
        Qed.

        Lemma indexing_updated_same {T F: Type} {_: Result.AssertionError F}: forall i (ls: list T) v ls',
          update v ls i = Success ls' -> Indexing.Nat.indexing ls' i = Success v.
        Proof.
          induction i; intros ls v ls' H; destruct ls; cbn in *; Result.assertion_failed_helper.
          - injection H as <-. reflexivity.
          - destruct (update v ls i) eqn:Eq_indexed; try discriminate.
            injection H as <-.
            specialize IHi with (1 := Eq_indexed) as <-.
            apply Indexing.Nat.cons.
        Qed.

       Lemma indexing_updated_other {T F: Type} {_: Result.AssertionError F}: forall i (ls: list T) v ls',
          update v ls i = Success ls' -> forall j, i <> j -> Indexing.Nat.indexing ls' j = Indexing.Nat.indexing ls j.
        Proof.
          induction i; intros ls v ls' H j Neq_i_j; destruct ls; cbn in *; Result.assertion_failed_helper.
          - injection H as <-. destruct j; try lia. reflexivity.
          - destruct (update v ls i) eqn:Eq_updated; try discriminate.
            injection H as <-.
            destruct j.
            + reflexivity.
            + repeat rewrite -> Indexing.Nat.cons.
              apply IHi with (1 := Eq_updated). lia.
        Qed.

        Lemma prop_preservation {T F: Type} {_: Result.AssertionError F}: forall (ls: list T) i v ls' P,
          Forall.Forall ls P ->
          P v ->
          update v ls i = Success ls' ->
          Forall.Forall ls' P.
        Proof.
          intros ls i v ls' P H Pv Eq_ls' j w Eq_indexed.
          destruct (Nat.eq_dec i j) as [ <- | Neq_i_j ].
          - apply indexing_updated_same in Eq_ls'.
            rewrite Eq_ls' in Eq_indexed. injection Eq_indexed as ->.
            assumption.
          - apply H with (i := j).
            rewrite <- Eq_indexed. symmetry.
            rewrite -> indexing_updated_other with (1 := Eq_ls') (2 := Neq_i_j).
            reflexivity.
        Qed.
      End One.

      Module Batch.
        Definition update {T F: Type} {_: Result.AssertionError F} (v: T) := Lextend (One.update v).

        Lemma step {T F: Type} {_: Result.AssertionError F}: forall (ls: list T) (i: nat) (is: list nat) (v: T),
          update v ls (i :: is) = let! ls' =<< One.update v ls i in update v ls' is.
        Proof. intros ls i is v. cbn. destruct is; cbn in *. - focus § _ _ [] § auto destruct; reflexivity. - reflexivity. Qed.

        Lemma failure_is_assertion {T F: Type} {f: Result.AssertionError F}: forall (is: list nat) (ls: list T) (v: T) (f': F),
          update v ls is = Result.Failure f' -> {| Result.f := f' |} = f.
        Proof.
          induction is; intros ls v f' H.
          - discriminate.
          - rewrite -> step in H. destruct (One.update v ls a) eqn:Eq_update.
            + apply IHis with (ls := s) (v := v). assumption.
            + apply One.failure_is_assertion in Eq_update. congruence.
        Qed.

        Lemma failure_bounds {T F: Type} {f: Result.AssertionError F}: forall (is: list nat) (ls: list T) (v: T) (f': F),
          @update T F f v ls is = Result.Failure f' -> ~ Forall.Forall is (fun i => i < length ls)%nat.
        Proof.
          induction is; intros; intros Falsum.
          - discriminate.
          - cbn in H. destruct (One.update v ls a) eqn:Eq_update.
            + specialize IHis with (1 := H). apply Forall.cons_inv_tail in Falsum. apply IHis. intros j w G. apply One.success_length in Eq_update as <-.
              specialize (Falsum j w). fforward. apply Falsum.
            + apply One.failure_bounds in Eq_update. specialize (Falsum 0%nat a). cbn in Falsum. fforward. lia.
        Qed.

        Lemma success_length {T F: Type} {_: Result.AssertionError F}: forall (is: list nat) (ls ls': list T) (v: T),
          update v ls is = Success ls' -> (length ls) = (length ls').
        Proof.
          induction is; intros ls0 ls2 v H; cbn in H.
          - injection H as <-. reflexivity.
          - destruct (One.update v ls0 a) as [ ls1 | ] eqn:Eq_ls1.
            + apply One.success_length in Eq_ls1 as ->.
              apply IHis with (v := v). apply H.
            + rewrite -> FoldResult.zero_failure0 in H. discriminate.
        Qed.

        Lemma prop_preservation {T F: Type} {_: Result.AssertionError F}: forall is (ls: list T) v ls' P,
          Forall.Forall ls P ->
          P v ->
          update v ls is = Success ls' ->
          Forall.Forall ls' P.
        Proof.
          induction is; intros ls v ls' P FP_ls P_v Eq_ls'.
          - cbn in Eq_ls'. injection Eq_ls' as <-. assumption.
          - cbn in Eq_ls'.
            destruct (One.update v ls a) eqn:Eq_update.
            + apply IHis with (ls := s) (v := v); try assumption.
              apply One.prop_preservation with (ls := ls) (i := a) (v := v); try assumption.
            + rewrite FoldResult.zero_failure0 in Eq_ls'. discriminate.
        Qed.

      End Batch.
    End Nat.
(* 
    Definition updating {T F: Type} (ls: list T) (i: Z) (v: T) {failure: Result.AssertionError F}: Result.Result (list T) F := match i with
    | Z0 => updating_nat ls 0 v
    | Zpos i => updating_nat ls (Pos.to_nat i) v
    | Zneg _ => Result.assertion_failed
    end.

    Definition batch_updating0_nat {T F: Type} {_: Result.AssertionError F} (ls: Result (list T) F) (is: list nat) (v: T) := List.FoldResult.fold_left_result0 (fun ls i => List.Updating.updating_nat ls i v) is ls.
    Definition batch_updating_nat {T F: Type} {_: Result.AssertionError F} (ls: list T) (is: list nat) (v: T) := List.FoldResult.fold_left_result (fun ls i => List.Updating.updating_nat ls i v) is ls.

    Definition batch_updating0 {T F: Type} {_: Result.AssertionError F} (ls: Result (list T) F) (is: list Z) (v: T) := List.FoldResult.fold_left_result0 (fun ls i => List.Updating.updating ls i v) is ls.
    Definition batch_updating {T F: Type} {_: Result.AssertionError F} (ls: list T) (is: list Z) (v: T) := List.FoldResult.fold_left_result (fun ls i => List.Updating.updating ls i v) is ls.

    Lemma batch_nat_cons {T F: Type} {_: Result.AssertionError F}: forall (ls: list T) (i: nat) (is: list nat) (v: T),
      batch_updating_nat ls (i :: is) v = let! ls' =<< updating_nat ls i v in batch_updating_nat ls' is v.
    Proof. intros ls i is v. unfold batch_updating_nat. rewrite -> FoldResult.cons. reflexivity. Qed.
    Lemma batch_cons {T F: Type} {_: Result.AssertionError F}: forall (ls: list T) (i: Z) (is: list Z) (v: T),
      batch_updating ls (i :: is) v = let! ls' =<< updating ls i v in batch_updating ls' is v.
    Proof. intros ls i is v. unfold batch_updating. rewrite -> FoldResult.cons. reflexivity. Qed.

    Lemma success_length_nat {T F: Type} {f: Result.AssertionError F}: forall (ls ls': list T) (i: nat) (v: T), updating_nat ls i v = Success ls' -> (length ls) = (length ls').
    Proof.
      intros ls. induction ls; intros ls' i v H.
      - Result.assertion_failed_helper.
      - destruct i.
        + injection H as <-. reflexivity.
        + cbn in *. destruct (updating_nat ls i v) eqn:Eq_updated; try discriminate.
          injection H as <-. cbn. f_equal.
          apply IHls with (1 := Eq_updated).
    Qed.

    Lemma success_length {T F: Type} {f: Result.AssertionError F}: forall (ls ls': list T) (i: Z) (v: T), updating ls i v = Success ls' -> (length ls) = (length ls').
    Proof. intros ls ls' i v H. induction i using pseudo_nat_ind. - apply success_length_nat with (1 := H). - apply success_length_nat with (1 := H). - Result.assertion_failed_helper. Qed.

    Lemma of_nat {T F: Type} {f: Result.AssertionError F}: forall (ls: list T) (i: nat) (v: T), updating_nat ls i v = updating ls (Z.of_nat i) v.
    Proof. intros. destruct i; cbn; try rewrite -> SuccNat2Pos.id_succ; reflexivity. Qed.

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

(*     Lemma failure_kind {T F: Type} {failure: Result.AssertionError F}: forall (ls: list T) (i: Z) (f: F) (v: T),
      updating ls i v = Result.Failure f -> updating ls i v = Result.assertion_failed.
    Proof. intros ls i f v H. destruct i. - apply failure_kind_nat with (f := f). apply H. - apply failure_kind_nat with (f := f). apply H. - Result.assertion_failed_helper. Qed.
 *)
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

    Lemma batch_failure_bounds {T F: Type} {f: Result.AssertionError F}: forall (is: list Z) (ls: list T) (v: T),
      @batch_updating T F f ls is v = Result.assertion_failed
      ->
      (exists j i, Indexing.indexing is j = Success i /\ (i < 0 \/ Z.of_nat (length ls) <= i) )%Z.
    Proof.
      assert (forall (is: list Z) (ls: list T) (v: T),
        @batch_updating T F f ls is v = Result.assertion_failed
        ->
        (exists j i, Indexing.indexing is j = Success i /\ (i < 0 \/ Z.of_nat (length ls) <= i) )%Z
      ) as LtR. {
        induction is; intros ls v Eq_failure.
        - Result.assertion_failed_helper.
        - rewrite batch_cons in Eq_failure.
          destruct (updating ls a v) eqn:Eq_updated.
          + apply IHis in Eq_failure. destruct Eq_failure as [ j [ i [ Eq_indexed Ineq_i ]]].
            pose proof (Indexing.success_bounds _ _ _ Eq_indexed) as B_j.
            exists (j + 1). exists i.
            split. * rewrite -> Indexing.cons0; [ apply Eq_indexed | lia ]. * apply Updating.success_length in Eq_updated. lia.
          + exists 0. exists a. split. * reflexivity. * rewrite <- failure_bounds with (v := v). Result.assertion_failed_helper.
      }
      apply LtR.
    Qed.
    
    Lemma batch_nat_failure_bounds {T F: Type} {f: Result.AssertionError F}: forall (is: list nat) (ls: list T) (v: T),
      @batch_updating_nat T F f ls is v = Result.assertion_failed
      ->
      (exists j i, Indexing.indexing is j = Success i /\ (length ls <= i))%nat.
    Proof.
      assert (forall (is: list nat) (ls: list T) (v: T),
        @batch_updating_nat T F f ls is v = Result.assertion_failed
        ->
        (exists j i, Indexing.indexing is j = Success i /\ (length ls <= i) )%nat
      ) as LtR. {
        induction is; intros ls v Eq_failure.
        - Result.assertion_failed_helper.
        - rewrite batch_nat_cons in Eq_failure.
          destruct (updating_nat ls a v) eqn:Eq_updated.
          + apply IHis in Eq_failure. destruct Eq_failure as [ j [ i [ Eq_indexed Ineq_i ]]].
            pose proof (Indexing.success_bounds _ _ _ Eq_indexed) as B_j.
            exists (j + 1). exists i.
            split. * rewrite -> Indexing.cons0; [ apply Eq_indexed | lia ]. * apply Updating.success_length_nat in Eq_updated. lia.
          + exists 0. exists a. split. * reflexivity. * rewrite <- failure_bounds_nat with (v := v). Result.assertion_failed_helper.
      }
      apply LtR.
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

    Lemma batch_failure_kind: forall {T F: Type} {failure: Result.AssertionError F} (is: list Z) (ls: list T) (f: F) (v: T),
      batch_updating ls is v = Result.Failure f -> batch_updating ls is v = Result.assertion_failed.
    Proof.
      induction is; intros ls f v H.
      - Result.assertion_failed_helper.
      - rewrite -> batch_cons.
        destruct (updating ls a v) eqn:Eq_updated.
        * rewrite -> Updating.batch_cons in H. rewrite -> Eq_updated in H. apply IHis with (1 := H).
        * pose proof (failure_kind _ _ _ _ Eq_updated) as Tmp. Result.assertion_failed_helper. rewrite -> Eq_updated in Tmp. injection Tmp as ->.
          reflexivity.
    Qed.

    Lemma success_bounds: forall {T F: Type} {failure: Result.AssertionError F} (ls: list T) (i: Z) (v: T),
      (exists ls', updating ls i v = Success ls') <-> (0 <= i /\ i < (Z.of_nat (length ls)) )%Z.
    Proof. intros T F f. split.
      - intros [ ls' H ]. pose proof (failure_bounds ls i) as [ _ Falsum ].
        destruct ( (0 <=? i) && (i <? Z.of_nat (length ls)))%Z eqn:Bounds.
        + Zhelper. lia.
        + hypotheses_reflector.
          * rewrite -> Z.leb_gt in H0. specialize (Falsum (or_introl H0)). destruct f. rewrite -> H in *. discriminate.
          * rewrite -> Z.ltb_ge in H0. specialize (Falsum (or_intror H0)). destruct f. rewrite -> H in *. discriminate.
      - intros [ Leq_0_i Le_i_len ]. pose proof (failure_bounds ls i v) as [ Falsum _ ].
        destruct i eqn:Eq_i.
        + destruct ls eqn:Eq_ls; cbn in *; try lia. exists (v :: l). reflexivity.
        + destruct (updating ls (Z.pos p) v) eqn:Eq_indexed in |- *.
          * exists s. reflexivity.
          * apply failure_kind in Eq_indexed. specialize (Falsum Eq_indexed).
            destruct Falsum; lia.
        + lia.
    Qed.

    Lemma nil {T F: Type} {failure: Result.AssertionError F}: forall (i: Z) (v: T), updating nil i v = Result.assertion_failed.
    Proof. intros. destruct i; reflexivity. Qed.

    Lemma cons_nat {T F: Type} {failure: Result.AssertionError F}: forall (t: list T) (h: T) (i: nat) (v: T),
      updating_nat (h :: t) (S i) v = (let! t' =<< updating_nat t i v in Success (h :: t')).
    Proof.
      induction t; intros h i v.
      - reflexivity.
      - destruct i eqn:Eq_i.
        + reflexivity.
        + rewrite -> IHt. reflexivity.
    Qed.

    Lemma cons {T F: Type} {failure: Result.AssertionError F}: forall (h: T) (t: list T) (i: Z) (v: T),
      0 <= i -> updating (h :: t) (i + 1) v = (let! t' =<< updating t i v in Success (h :: t')).
    Proof.
      intros h t i v Ineq_i.
      destruct i eqn:Eq_i; cbn -[updating_nat].
      - assert (Pos.to_nat 1 = 1%nat) as -> by lia.
        rewrite -> cons_nat. reflexivity.
      - assert (Pos.to_nat (p + 1) = S (Pos.to_nat p)) as -> by lia.
        rewrite -> cons_nat. reflexivity.
      - lia.
    Qed.

    Lemma cons_of_nat {T F: Type} {failure: Result.AssertionError F}: forall (h: T) (t: list T) (i: nat) (v: T),
      updating (h :: t) (Z.of_nat (S i)) v = (let! t' =<< updating t (Z.of_nat i) v in Success (h :: t')).
    Proof. intros h t i v. assert (Z.of_nat (S i) = Z.of_nat i + 1) as -> by lia. apply cons. lia. Qed.

    Lemma indexing_updated_same {T F: Type} {failure: Result.AssertionError F}: forall i (ls: list T) v ls',
      updating ls i v = Success ls' -> Indexing.indexing ls' i = Success v.
    Proof.
      induction i using pseudo_nat_ind; intros ls v ls' H; (destruct ls; [ Result.assertion_failed_helper | ]).
      - injection H as [=<-]. reflexivity.
      - cbn in H. rewrite -> SuccNat2Pos.id_succ in H.
        focus § _ [] _ § auto destruct in H.
        injection H as [=<-].
        rewrite -> Indexing.cons_of_nat_succ.
        apply IHi with (ls := ls).
        rewrite <- Updating.of_nat. assumption.
      - Result.assertion_failed_helper.
    Qed.

    Lemma indexing_updated_other {T F: Type} {failure: Result.AssertionError F}: forall i (ls: list T) v ls',
      updating ls i v = Success ls' -> forall j, i <> j -> Indexing.indexing ls' j = Indexing.indexing ls j.
    Proof.
      induction i using pseudo_nat_ind; intros ls v ls' H j Ineq_j; (destruct ls; [ solve[ Result.assertion_failed_helper ] | ]).
      - injection H as [=<-]. induction j using pseudo_nat_ind.
        + lia.
        + focus § _ _ [] § do (fun t => destruct t eqn:Eq_indexed).
          * rewrite -> Indexing.cons_of_nat_succ in *. assumption.
          * replace (Z.of_nat (S n)) with ((Z.of_nat n) + 1) in * by lia.
            rewrite -> Indexing.cons0 in * by lia.
            assumption.
        + cbn. reflexivity.
      - rewrite -> cons_of_nat in H. focus § _ [] _ § auto destruct in H.
        injection H as <-.
        destruct j; try reflexivity.
        assert (Z.pos p = (Z.pos p - 1) + 1) as -> by lia.
        do 2 rewrite -> Indexing.cons0 by lia.
        apply IHi with (v := v).
        + assumption.
        + lia.
      - Result.assertion_failed_helper.
    Qed.

    Lemma prop_preservation {T F: Type} {failure: Result.AssertionError F}: forall (ls: list T) i v ls' P,
      Forall ls P ->
      P v ->
      updating ls i v = Success ls' ->
      Forall ls' P.
    Proof.
      intros ls i v ls' P H Pv Eq_ls' j w Eq_indexed.
      destruct (Z.eq_dec i j) as [ Eq_ij | Neq_ij ].
      - subst. apply indexing_updated_same in Eq_ls'.
        rewrite Eq_ls' in *. injection Eq_indexed as ->.
        assumption.
      - apply H with (i := j).
        rewrite <- Eq_indexed. symmetry.
        apply indexing_updated_other with (1 := Eq_ls') (2 := Neq_ij).
    Qed.
    

    Lemma batch_equiv {T F: Type} {_: Result.AssertionError F}: forall ls is v,
      @batch_updating0 T F _ (Success ls) is v = @batch_updating T F _ ls is v.
    Proof. reflexivity. Qed.

    Lemma batch_prop_preservation {T F: Type} {failure: Result.AssertionError F}: forall is (ls: list T) v ls' P,
      Forall ls P ->
      P v ->
      batch_updating ls is v = Success ls' ->
      Forall ls' P.
    Proof.
      induction is; intros ls v ls' P FP_ls P_v Eq_ls'.
      - cbn in Eq_ls'. injection Eq_ls' as <-. assumption.
      - cbn in Eq_ls'.
        focus § _ [] _ § replace with (batch_updating0 (updating ls a v) is v) in Eq_ls'.
        destruct (updating ls a v) eqn:Eq_updated.
        + apply IHis with (2 := P_v) (3 := Eq_ls').
          intros i w Eq_indexed.
          destruct (Z.eq_dec a i) as [ Eq_ai | Neq_ai ].
          * subst. pose proof (indexing_updated_same _ _ _ _ Eq_updated).
            assert (v = w) as -> by congruence. assumption.
          * pose proof (indexing_updated_other _ _ _ _ Eq_updated _ Neq_ai).
            apply (FP_ls i w). congruence.
        + pose proof (FoldResult.zero_failure0 (fun ls i => updating ls i v) is f).
          unfold batch_updating0 in Eq_ls'. congruence.
    Qed.
  End Updating. *)
  End Update.

  Module Exists.
    Fixpoint exist {T F: Type} (ls: list T) (p: T -> Result bool F): Result bool F := match ls with
    | nil => Success false
    | h :: t => let! b: bool =<< p h in if b then Success true else exist t p
    end.

    Lemma failure_kind {T F: Type} {_: Result.AssertionError F}: forall ls p f,
      @exist T F ls p = Failure f -> exists i v, Indexing.Int.indexing ls i = Success v /\ p v = Failure f.
    Proof.
      induction ls; intros p f Ex; try discriminate.
      cbn in Ex. destruct (p a) as [ [ | ] | ] eqn:Eq.
      - discriminate.
      - specialize IHls with (1 := Ex). destruct IHls as [ i [ v [ Indexed ]]].
        exists (i+1). exists v.
        rewrite -> Indexing.Int.cons.
        + split; assumption.
        + apply Indexing.Int.success_bounds in Indexed. destruct Indexed as [ Indexed _ ]. apply Indexed.
      - injection Ex as ->. exists 0. exists a. cbn. split; [ reflexivity | assumption].
    Qed.
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
        Indexing.Int.indexing (range b l) i = Success v -> v = (b + i).
      Proof.
        induction i using pseudo_nat_ind.
        - intros. cbn in *.
          destruct l; try Result.assertion_failed_helper. cbn in *.
          injection H as [=->]. lia.
        - intros. cbn in *. rewrite -> SuccNat2Pos.id_succ in H.
          destruct l; try Result.assertion_failed_helper. cbn in *.
          specialize (IHi (b + 1) l). cbn in IHi.
          rewrite -> Indexing.Int.of_nat in *. specialize (IHi _ H).
          lia.
        - intros. cbn in H. Result.assertion_failed_helper.
      Qed.
    End Impl.

    Definition IsRange (from to: Z) (ls: list Z) :=
      (forall (F: Type) (f: Result.AssertionError F) z, from <= z < to -> Indexing.Int.indexing ls (z - from) = Success z).

    Definition range(from to: Z) := Impl.range from (Z.to_nat (to - from)).

    Lemma length: forall s e, length (range s e) = Z.to_nat (e - s).
    Proof. unfold range. intros. apply Impl.length. Qed.

    Lemma indexing {F: Type} {f: Result.AssertionError F}: forall s e i v,
      Indexing.Int.indexing (range s e) i = Success v -> v = (s + i).
    Proof. unfold range. intros. apply Impl.indexing with (1 := H). Qed.

    Lemma completeness {F: Type} {f: Result.AssertionError F}: forall s e z, s <= z -> z < e -> exists i, Indexing.Int.indexing (range s e) i = Success z.
    Proof.
      intros. remember (z - s) as i.
      exists i.
      assert (0 <= i < Z.of_nat (Z.to_nat (e - s))) as Bounds_z by lia.
      rewrite <- length in Bounds_z.
      destruct (Indexing.Int.indexing (range s e) i) eqn:Eq.
      - apply indexing in Eq. f_equal. lia.
      - apply Indexing.Int.failure_bounds in Eq. lia.
    Qed.

    Lemma range_sortedness {F: Type} {f: Result.AssertionError F}: forall s e i0 i1 z0 z1,
      (i0 <= i1)%Z ->
      Indexing.Int.indexing (range s e) i0 = Success z0 ->
      Indexing.Int.indexing (range s e) i1 = Success z1 ->
      (z0 <= z1)%Z.
    Proof. intros. apply indexing in H0. apply indexing in H1. lia. Qed.
  End Range.
End List.