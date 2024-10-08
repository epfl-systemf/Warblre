From Coq Require Import ZArith Lia List Bool.
From Warblre Require Import Tactics Focus Result.

Import Result.Notations.

(** Contains some extra operations and list,
    mostly involving the Result monad,
    and many lemmas about these operations.
*)

Module List.
  Local Close Scope nat.
  Local Open Scope Z.
  Local Open Scope result_flow.

  Definition empty {T: Type} := @nil T.

  Fixpoint take {A: Type} (l: list A) (len: nat) : list A :=
    match len with
    | 0%nat => nil
    | S len' =>
        match l with
        | nil => nil
        | e :: l' => e :: (take l' len')
        end
    end.

  Fixpoint drop {A: Type} (l: list A) (count: nat) : list A :=
    match count with
    | 0%nat => l
    | S len' =>
        match l with
        | nil => nil
        | e :: l' => drop l' len'
        end
    end.

  Lemma rec_eq {T: Type}: forall (l: list T) a, a :: l = l -> False.
  Proof. intros l a H. apply (@f_equal _ _ (@length _) _ _) in H. cbn in H. apply Nat.neq_succ_diag_l in H. assumption. Qed.
  Ltac rec_eq := solve [ exfalso; apply rec_eq with (1 := ltac:(eassumption)) ].

  Lemma app_cons {A: Type}: forall l (h: A) r, l ++ (h :: r) = (l ++ (h :: nil)) ++ r.
  Proof. induction l; intros h r. - reflexivity. - cbn. f_equal. apply IHl. Qed.

  Lemma same_tail {T: Type}: forall (t: list T) p0 p1 h0 h1, p0 ++ h0 :: t = p1 ++ h1 :: t -> h0 = h1.
  Proof. intros. rewrite -> (app_cons p0) in H. rewrite -> (app_cons p1) in H. apply app_inv_tail in H. apply app_inj_tail in H as [_ ?]. assumption. Qed.

  Lemma mutual_prefixes {T: Type}: forall (l1 l2 p12 p21: list T), l1 = p12 ++ l2 -> l2 = p21 ++ l1 -> l1 = l2.
  Proof.
    intros l1 l2 p12 p21 Eq_l1 Eq_l2. 
    pose proof (@f_equal _ _ (@length _) _ _ Eq_l1). pose proof (@f_equal _ _ (@length _) _ _ Eq_l2).
    rewrite -> app_length in *.
    assert (length p12 = 0)%nat as Eq_p12 by lia. assert (length p21 = 0)%nat as Eq_p21 by lia.
    rewrite -> length_zero_iff_nil in *. subst. reflexivity.
  Qed.

  Module Slice.
    (* From is inclusive, to is exclusive *)
    Definition sublist {A: Type} (l: list A) (from to: nat) : list A := take (drop l from) (to - from).
  End Slice.

  Module Unique.
    Definition unique {T F: Type} {_: Result.AssertionError F} (ls: list T): Result T F := match ls with
      | h :: nil => Success h
      | _ => Result.assertion_failed
      end.

    Lemma success {T F: Type} {_: Result.AssertionError F}: forall (ls: list T) v, unique ls = Success v -> ls = v :: nil.
    Proof. intros. destruct ls; cbn. - Result.assertion_failed_helper. - destruct ls. + cbn in H. injection H as <-. reflexivity. + Result.assertion_failed_helper. Qed.

    Lemma failure_bounds {T F: Type} {_: Result.AssertionError F}: forall (ls: list T) f, unique ls = Error f -> (length ls <> 1)%nat.
    Proof. intros. destruct ls; cbn. - lia. - destruct ls; cbn. + discriminate. + lia. Qed.

    Lemma head {T F: Type} {_: Result.AssertionError F}: forall h (t: list T) v, unique (h :: t) = Success v -> h = v.
    Proof. intros. destruct t; cbn in *. - injection H as <-. reflexivity. - Result.assertion_failed_helper. Qed.
  End Unique.

  Module FoldResult.
    Fixpoint fold_left_result0 {S T F: Type} (r: T -> S -> Result T F) (ls: list S) (racc: Result T F): Result T F := match ls with
      | nil => racc
      | s :: ls' => let! acc =<< racc in fold_left_result0 r ls' (r acc s)
      end.

    Definition fold_left_result {S T F: Type} (r: T -> S -> Result T F) (ls: list S) (zero: T): Result T F :=
      fold_left_result0 r ls (Success zero).

    Lemma zero_failure0 {S T F: Type}: forall (r: T -> S -> Result T F) (ls: list S) (f: F), fold_left_result0 r ls (Error f) = (Error f).
    Proof. intros r ls f. destruct ls; reflexivity. Qed.

    Lemma cons0 {S T F: Type}: forall (r: T -> S -> Result T F) (h: S) (t: list S) (zero: Result T F),
      fold_left_result0 r (h :: t) zero = let! zero' =<< zero in fold_left_result0 r t (r zero' h).
    Proof. intros r h t zero. reflexivity. Qed.

    Lemma cons {S T F: Type}: forall (r: T -> S -> Result T F) (h: S) (t: list S) (acc: T),
      fold_left_result r (h :: t) acc = let! acc' =<< r acc h in fold_left_result r t acc'.
    Proof. intros r h t acc. destruct t. - cbn; destruct (r acc h); reflexivity. - cbn. reflexivity. Qed.
  End FoldResult.

  Definition lift_to_Z {T U F: Type} `{Result.AssertionError F} (f: list T -> nat -> Result U F): list T -> Z -> Result U F :=
    fun ls i => match i with
                | Z0 => f ls 0%nat
                | Zpos i => f ls (Pos.to_nat i)
                | Zneg _ => Result.assertion_failed
                end.

  Definition lift_to_list {T F I: Type} `{Result.AssertionError F} (f: T -> I -> Result T F): T -> list I -> Result T F :=
    fun init ls => List.FoldResult.fold_left_result0 f ls (Success init).

  Module Indexing.
    Module Nat.
      Definition indexing {T F: Type} {failure: Result.AssertionError F} (ls: list T) (i: nat): Result.Result T F :=
        Result.Conversions.from_option (List.nth_error ls i).

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
        indexing ls i = Result.Error f' -> {| Result.f := f' |} = f.
      Proof.
        intros ls i f' Eq_indexed. unfold indexing in *. 
        destruct (List.nth_error _ _) in *; try discriminate.
        cbn in Eq_indexed. Result.assertion_failed_helper.
      Qed.

      Lemma failure_kind {T F: Type} {_: Result.AssertionError F}: forall (ls: list T) (i: nat) (f: F),
        indexing ls i = Result.Error f -> indexing ls i = Result.assertion_failed.
      Proof. intros ls i f H. pose proof (failure_is_assertion ls i f H) as [=]. Result.assertion_failed_helper. Qed.

      Lemma failure_rewrite {T F: Type} {_: Result.AssertionError F}: forall (ls: list T) (i: nat) (f: F),
        indexing ls i = Result.Error f -> indexing ls i = Result.assertion_failed /\ @Result.Error T F f = Result.assertion_failed.
      Proof. intros ls i f H. pose proof (failure_is_assertion ls i f H) as [=]. Result.assertion_failed_helper. Qed.

      Lemma failure_bounds0 {T F: Type} {f: Result.AssertionError F}: forall (ls: list T) (i: nat), @indexing T F f ls i = Result.assertion_failed <-> (length ls <= i )%nat.
      Proof.
        destruct f as [f]. intros ls i. rewrite <- nth_error_None.
        unfold indexing.
        destruct (nth_error ls i) eqn:Eq; cbn in *.
        - split; discriminate.
        - split; reflexivity.
      Qed.
      Lemma failure_bounds {T F: Type} {f: Result.AssertionError F}: forall (ls: list T) (i: nat) (f': F), @indexing T F f ls i = Result.Error f' -> (length ls <= i )%nat.
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

      Lemma concat' {T F: Type} {_: Result.AssertionError F}: forall (tl tr: list T) (i: nat),
        (i < List.length tl /\ indexing (tl ++ tr) i = indexing tl i)%nat \/
        (List.length tl <= i /\ indexing (tl ++ tr) i = indexing tr (i - List.length tl))%nat.
      Proof.
        unfold indexing.
        intros tl tr i.
        destruct (lt_dec i (List.length tl)).
        - left. split; [ assumption | ]. rewrite -> nth_error_app1 by assumption. reflexivity.
        - right. assert (List.length tl <= i)%nat by lia. split; [ assumption | ].
          rewrite -> nth_error_app2 by assumption. reflexivity.
      Qed.

      Lemma concat {T F: Type} {_: Result.AssertionError F}: forall (tl tr: list T) (i: nat) v,
        indexing (tl ++ tr) i = v ->
        (i < List.length tl /\  v = indexing tl i)%nat \/
        (List.length tl <= i /\ v = indexing tr (i - List.length tl))%nat.
      Proof.
        intros. destruct (concat' tl tr i) as [[ ? ?] | [ ? ? ]]; subst; [left; split | right; split]; assumption.
      Qed.

      Lemma concat_left {T F: Type} {_: Result.AssertionError F}: forall (i: nat) (tl tr: list T) v, indexing tl i = Success v -> indexing (tl ++ tr) (i)%nat = Success v.
      Proof.
        induction i; intros tl tr v H.
        - destruct tl. + rewrite nil in H. Result.assertion_failed_helper. + cbn in *. assumption.
        - destruct tl. + rewrite nil in H. Result.assertion_failed_helper. + cbn in *. rewrite -> cons in *. apply IHi. assumption.
      Qed.
      Lemma concat_right {T F: Type} {_: Result.AssertionError F}: forall (tl tr: list T) (i: nat) v, indexing tr i = v -> indexing (tl ++ tr) (length tl + i)%nat = v.
      Proof. induction tl; intros. - assumption. - cbn. rewrite -> cons. apply IHtl. assumption. Qed.

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
      Definition indexing {T F: Type} {_: Result.AssertionError F}: list T -> Z -> Result.Result T F := lift_to_Z Nat.indexing.

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
          indexing ls i = Result.Error f' -> {| Result.f := f' |} = f.
      Proof.
        unfold indexing. intros ls i f' Eq_indexed. destruct i.
        - apply Nat.failure_is_assertion in Eq_indexed. assumption.
        - apply Nat.failure_is_assertion in Eq_indexed. assumption.
        - cbn in Eq_indexed. Result.assertion_failed_helper.
      Qed.

      Lemma failure_kind {T F: Type} {_: Result.AssertionError F}: forall (ls: list T) (i: Z) (f: F),
        indexing ls i = Result.Error f -> indexing ls i = Result.assertion_failed.
      Proof. intros ls i f H. pose proof (failure_is_assertion ls i f H) as [=]. Result.assertion_failed_helper. Qed.

      Lemma failure_rewrite {T F: Type} {_: Result.AssertionError F}: forall (ls: list T) (i: Z) (f: F),
        indexing ls i = Result.Error f -> indexing ls i = Result.assertion_failed /\ @Result.Error T F f = Result.assertion_failed.
      Proof. intros ls i f H. pose proof (failure_is_assertion ls i f H) as [=]. Result.assertion_failed_helper. Qed.

      Lemma failure_bounds0 {T F: Type} {f: Result.AssertionError F}: forall (ls: list T) (i: Z), @indexing T F f ls i = Result.assertion_failed <-> (i < 0 \/ (Z.of_nat (length ls)) <= i )%Z.
      Proof.
        unfold indexing. intros ls i. destruct i.
        - unfold lift_to_Z. rewrite -> Nat.failure_bounds0. lia.
        - unfold lift_to_Z. rewrite -> Nat.failure_bounds0. lia.
        - cbn. split. + lia. + reflexivity.
      Qed.

      Lemma failure_bounds {T F: Type} {f: Result.AssertionError F}: forall (ls: list T) (i: Z) (f': F), @indexing T F f ls i = Result.Error f' -> (i < 0 \/ (Z.of_nat (length ls)) <= i )%Z.
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
    Proof. intros h t P F_h_t. specialize (F_h_t 0%nat h). cbn in *. auto. Qed.

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
          update v ls i = Result.Error f' -> {| Result.f := f' |} = f.
        Proof.
          induction ls; intros i v f'.
          - cbn. Result.assertion_failed_helper. intros [=<-]. reflexivity.
          - destruct i.
            + discriminate.
            + intros H. cbn in H. destruct (update v ls i) eqn:Eq_update; try discriminate.
              injection H as <-. apply IHls with (i := i) (v := v). assumption.
        Qed.

        Lemma failure_kind {T F: Type} {_: Result.AssertionError F}: forall (ls: list T) (i: nat) (v: T) (f: F),
          update v ls i = Result.Error f -> update v ls i = Result.assertion_failed.
        Proof. intros ls i v f H. pose proof (failure_is_assertion ls i v f H) as [=]. Result.assertion_failed_helper. Qed.

        Lemma failure_bounds0 {T F: Type} {f: Result.AssertionError F}: forall (ls: list T) (i: nat) (v: T),
          @update T F f v ls i = Result.assertion_failed <-> (length ls <= i)%nat.
        Proof.
          induction ls; intros i v; split; intros H.
          - cbn. lia.
          - reflexivity.
          - destruct i. + Result.assertion_failed_helper. + cbn in H. destruct (update v ls i) eqn:Eq; Result.assertion_failed_helper. injection H as <-. rewrite -> IHls in Eq. cbn. lia.
          - destruct i. + Result.assertion_failed_helper. + cbn in H|-*. apply le_S_n in H. rewrite <- (IHls i v) in H. rewrite -> H. Result.assertion_failed_helper.
        Qed.

        Lemma failure_bounds {T F: Type} {f: Result.AssertionError F}: forall (ls: list T) (i: nat) (v: T) (f': F),
          @update T F f v ls i = Result.Error f' -> (length ls <= i)%nat.
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
        Definition update {T F: Type} {_: Result.AssertionError F} (v: T) := lift_to_list (One.update v).

        Lemma step {T F: Type} {_: Result.AssertionError F}: forall (ls: list T) (i: nat) (is: list nat) (v: T),
          update v ls (i :: is) = let! ls' =<< One.update v ls i in update v ls' is.
        Proof. intros ls i is v. cbn. destruct (One.update v ls i) eqn:Eq. - reflexivity. - destruct is; reflexivity. Qed.

        Lemma failure_is_assertion {T F: Type} {f: Result.AssertionError F}: forall (is: list nat) (ls: list T) (v: T) (f': F),
          update v ls is = Result.Error f' -> {| Result.f := f' |} = f.
        Proof.
          induction is; intros ls v f' H.
          - discriminate.
          - rewrite -> step in H. destruct (One.update v ls a) eqn:Eq_update.
            + apply IHis with (ls := s) (v := v). assumption.
            + injection H as <-. apply One.failure_is_assertion in Eq_update. assumption.
        Qed.

        Lemma failure_bounds {T F: Type} {f: Result.AssertionError F}: forall (is: list nat) (ls: list T) (v: T) (f': F),
          @update T F f v ls is = Result.Error f' -> ~ Forall.Forall is (fun i => i < length ls)%nat.
        Proof.
          induction is; intros; intros Falsum.
          - discriminate.
          - cbn in H. destruct (One.update v ls a) eqn:Eq_update.
            + specialize IHis with (1 := H). apply Forall.cons_inv_tail in Falsum. apply IHis. intros j w G. apply One.success_length in Eq_update as <-.
              specialize (Falsum j w). auto.
            + apply One.failure_bounds in Eq_update. specialize (Falsum 0%nat a). cbn in Falsum. fforward Falsum. lia.
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
  End Update.

  Module Exists.
    Definition Exist {T F: Type} {_: Result.AssertionError F} (ls: list T) (p: T -> Prop): Prop := exists i v, Indexing.Nat.indexing ls i = Success v /\ p v.
    Definition ExistValue {T F: Type} {_: Result.AssertionError F} (ls: list T) (v: T): Prop := exists i, Indexing.Nat.indexing ls i = Success v.

    Fixpoint exist {T F: Type} (ls: list T) (p: T -> Result bool F): Result bool F := match ls with
    | nil => Success false
    | h :: t => let! b: bool =<< p h in if b then Success true else exist t p
    end.

    Lemma failure_kind {T F: Type} {_: Result.AssertionError F}: forall ls p f,
      @exist T F ls p = Error f -> exists i v, Indexing.Int.indexing ls i = Success v /\ p v = Error f.
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

    Lemma cons_head {T F: Type} {_: Result.AssertionError F}: forall (h: T) ls p, p h -> Exist (h :: ls) p.
    Proof. intros h ls p H. exists 0%nat. exists h. split; [ reflexivity | assumption ]. Qed.
    Lemma cons_tail {T F: Type} {_: Result.AssertionError F}: forall (h: T) ls p, Exist ls p -> Exist (h :: ls) p.
    Proof. intros h ls p (i & v & ?). exists (S i)%nat. exists v. rewrite -> List.Indexing.Nat.cons. assumption. Qed.
    Lemma concat_right {T F: Type} {_: Result.AssertionError F}: forall (ls0 ls1: list T) p, Exist ls0 p -> Exist (ls0 ++ ls1) p.
    Proof. intros ls0 ls1 p (i & v & H0 & H1). exists i. exists v. split; [ | assumption ]. apply Indexing.Nat.concat_left. assumption. Qed.
    Lemma concat_left {T F: Type} {_: Result.AssertionError F}: forall (ls0 ls1: list T) p, Exist ls1 p -> Exist (ls0 ++ ls1) p.
    Proof. intros ls0 ls1 p (i & v & H0 & H1). exists (List.length ls0 + i)%nat. exists v. split; [ | assumption ]. apply Indexing.Nat.concat_right. assumption. Qed.

    Lemma cons_inv {T F: Type} {_: Result.AssertionError F}: forall (h: T) ls p, Exist (h :: ls) p -> p h \/ Exist ls p.
    Proof.
      intros h ls p ([ | i] & v & Eq_indexed & ?).
      - cbn in Eq_indexed. injection Eq_indexed as <-. left. assumption.
      - rewrite -> Indexing.Nat.cons in Eq_indexed. right. exists i. exists v. split; assumption.
    Qed.

    Lemma concat_inv {T F: Type} {_: Result.AssertionError F}: forall (ls0 ls1: list T) p, Exist (ls0 ++ ls1) p -> Exist ls0 p \/ Exist ls1 p.
    Proof.
      induction ls0; intros ls1 p (i & v & Eq_indexed & Eq_v).
      - rewrite -> app_nil_l in Eq_indexed. right. exists i. exists v. split; assumption.
      - destruct i as [ | i ].
        + cbn in Eq_indexed. injection Eq_indexed as <-. left. exists 0%nat. exists a. split; [ reflexivity | assumption ].
        + cbn in Eq_indexed. rewrite -> Indexing.Nat.cons in Eq_indexed.
          pose proof (conj Eq_indexed Eq_v) as W.
          pattern v in W. apply ex_intro in W. pattern i in W. apply ex_intro in W.
          destruct (IHls0 _ _ W) as [ H | H ].
          * left. apply cons_tail. assumption.
          * right. assumption.
    Qed.

    Lemma exist_value_eq {T F: Type} {_: Result.AssertionError F}: forall ls v, Exist ls (fun (v': T) => v = v') <-> ExistValue ls v.
    Proof.
      unfold Exist,ExistValue.
      intros ls v; split; intros H.
      - destruct H as (i & v' & Eq_indexed & <-). exists i. assumption.
      - destruct H as (i & Eq_indexed). exists i. exists v. split; [ assumption | reflexivity ].
    Qed.

    Lemma true_to_prop {T F: Type} {_: Result.AssertionError F}: forall ls (p: T -> Result bool F), exist ls p = Success true -> Exist ls (fun v => p v = Success true).
    Proof.
      induction ls; intros p H.
      - Result.assertion_failed_helper.
      - destruct (p a) as [ [ | ] | f ] eqn:Eq_pa.
        + exists 0%nat. exists a. split; [ reflexivity | assumption ].
        + cbn in H. rewrite -> Eq_pa in H. apply cons_tail. apply IHls. apply H.
        + cbn in H. rewrite -> Eq_pa in H. discriminate.
    Qed.

    Lemma false_to_prop {T F: Type} {_: Result.AssertionError F}: forall ls (p: T -> Result bool F), exist ls p = Success false -> Forall.Forall ls (fun v => p v = Success false).
    Proof.
      induction ls; intros p H i v Eq_indexed.
      - rewrite -> Indexing.Nat.nil in Eq_indexed. Result.assertion_failed_helper.
      - destruct (p a) as [ [ | ] | f ] eqn:Eq_pa.
        + cbn in H. rewrite -> Eq_pa in H. discriminate.
        + destruct i.
          * injection Eq_indexed as <-. assumption.
          * cbn in H. rewrite -> Eq_pa in H. rewrite -> Indexing.Nat.cons in Eq_indexed. unfold Forall.Forall in IHls. apply IHls with (1 := H) (2 := Eq_indexed).
        + cbn in H. rewrite -> Eq_pa in H. discriminate.
    Qed.
  End Exists.

  Module Sublist.
    Definition sublist {T F: Type} {_: Result.AssertionError F} (l r: list T): Prop := Forall.Forall l (fun e => exists i, Indexing.Nat.indexing r i = Success e).

    Lemma refl {T F: Type} {_: Result.AssertionError F}: forall (l: list T), sublist l l.
    Proof. intros l i v Eq_indexed. exists i. assumption. Qed.

    Lemma trans {T F: Type} {_: Result.AssertionError F}: forall (l0 l1 l2: list T), sublist l0 l1 -> sublist l1 l2 -> sublist l0 l2.
    Proof. intros l0 l1 l2 S_01 S_12 i v Eq_indexed. specialize (S_01 _ _ Eq_indexed) as (i' & Eq_indexed'). specialize (S_12 _ _ Eq_indexed'). assumption. Qed.

    Lemma cons_super {T F: Type} {_: Result.AssertionError F}: forall (l r: list T) h, sublist l r -> sublist l (h :: r).
    Proof. intros l r h S_lr i v Eq_indexed. specialize (S_lr _ _ Eq_indexed) as (i' & Eq_indexed'). exists (S i'). rewrite -> Indexing.Nat.cons. assumption. Qed.

    Lemma concat_super_left {T F: Type} {_: Result.AssertionError F}: forall (l r r': list T), sublist l r -> sublist l (r' ++ r).
    Proof. intros l r r' S_lr i v Eq_indexed. specialize (S_lr _ _ Eq_indexed) as (i' & Eq_indexed'). apply Indexing.Nat.concat_right with (tl := r') in Eq_indexed'. exists (List.length r' + i')%nat. assumption. Qed.
    Lemma concat_super_right {T F: Type} {_: Result.AssertionError F}: forall (l r r': list T), sublist l r -> sublist l (r ++ r').
    Proof. intros l r r' S_lr i v Eq_indexed. specialize (S_lr _ _ Eq_indexed) as (i' & Eq_indexed'). apply Indexing.Nat.concat_left with (tr := r') in Eq_indexed'. exists i'. assumption. Qed.

    Lemma exist {T F: Type} {_: Result.AssertionError F}: forall (l: list T) r p, sublist l r -> Exists.Exist l p -> Exists.Exist r p.
    Proof. intros l r p S_lr (i & v & Eq_indexed & P_v). unfold sublist,Forall.Forall in S_lr. specialize (S_lr _ _ Eq_indexed) as (i' & Eq_indexed'). exists i'. exists v. split; assumption. Qed.
  End Sublist.

  Module Filter.
    Fixpoint filter {T F: Type} (ls: list T) (f: T -> Result bool F): Result (list T) F := match ls with
      | nil => Success nil
      | h :: t =>
        let! b: bool =<< f h in
        let! t' =<< filter t f in
        if b then
          Success (h :: t')
        else
          Success t'
      end.

    Lemma failure_kind {T F: Type} {_: Result.AssertionError F}: forall ls g f,
      @filter T F ls g = Error f -> exists i v, Indexing.Nat.indexing ls i = Success v /\ g v = Error f.
    Proof.
      induction ls; intros g f Ex; try discriminate.
      cbn in Ex. destruct (g a) as [ [ | ] | ] eqn:Eq.
      - destruct (filter ls g) eqn:Eq_rec.
        + discriminate.
        + injection Ex as ->. specialize IHls with (1 := Eq_rec) as [ i [ v [ Eq_indexed Eq_filter ]]].
          exists (S i). exists v. split; assumption.
      - destruct (filter ls g) eqn:Eq_rec.
        + discriminate.
        + injection Ex as ->. specialize IHls with (1 := Eq_rec) as [ i [ v [ Eq_indexed Eq_filter ]]].
          exists (S i). exists v. split; assumption.
      - injection Ex as ->. exists 0%nat. exists a. cbn. split; [ reflexivity | assumption].
    Qed.
  End Filter.

  Module Range.
    Module Nat.
      Definition IsRange (from to: nat) (ls: list nat) :=
        (forall (F: Type) (f: Result.AssertionError F) z, (from <= z < to)%nat -> Indexing.Nat.indexing ls (z - from)%nat = Success z).

      Module Length.
        Fixpoint range (base: nat) (l: nat) := match l with
        | 0%nat => nil
        | S l' => base :: (range (base + 1) l')
        end.

        Lemma length: forall l b, length (range b l) = l.
        Proof. induction l; intros b; cbn. - reflexivity. - rewrite -> IHl. reflexivity. Qed.

        Lemma indexing {F: Type} {f: Result.AssertionError F}: forall i b l v,
          Indexing.Nat.indexing (range b l) i = Success v -> v = (b + i)%nat.
        Proof.
          induction i.
          - intros. cbn in *.
            destruct l; try Result.assertion_failed_helper. cbn in *.
            injection H as [=->]. lia.
          - intros. cbn in *.
            destruct l; try Result.assertion_failed_helper. cbn in *.
            specialize (IHi (b + 1)%nat l). cbn in IHi. specialize (IHi _ H). lia.
        Qed.

        Lemma completeness {F: Type} {f: Result.AssertionError F}: forall s l z, (s <= z)%nat -> (z < s + l)%nat -> exists i, Indexing.Nat.indexing (range s l) i = Success z.
        Proof.
          intros. remember (z - s)%nat as i.
          exists i.
          assert (0 <= i < l)%nat as Bounds by lia.
          rewrite <- length with (b := s) (l := l) in Bounds.
          destruct (Indexing.Nat.indexing (range s l) i) eqn:Eq.
          - apply indexing in Eq. f_equal. lia.
          - apply Indexing.Nat.failure_bounds in Eq. lia.
        Qed.
      End Length.

      Module Bounds.
        Definition range(from to: nat) := Length.range from (to - from)%nat.

        Lemma length: forall s e, length (range s e) = (e - s)%nat.
        Proof. unfold range. intros. apply Length.length. Qed.

        Lemma indexing {F: Type} {f: Result.AssertionError F}: forall s e i v,
          Indexing.Nat.indexing (range s e) i = Success v -> v = (s + i)%nat.
        Proof. unfold range. intros. apply Length.indexing with (1 := H). Qed.

        Lemma completeness {F: Type} {f: Result.AssertionError F}: forall s e z, (s <= z)%nat -> (z < e)%nat -> exists i, Indexing.Nat.indexing (range s e) i = Success z.
        Proof. unfold range. intros. apply Length.completeness; lia. Qed.
      End Bounds.
    End Nat.

    Module Int.
      Definition IsRange (from to: Z) (ls: list Z) :=
        (forall (F: Type) (f: Result.AssertionError F) z, (from <= z < to)%Z -> Indexing.Int.indexing ls (z - from)%Z = Success z).

      Module Length.
        Fixpoint range (base: Z) (l: nat) := match l with
        | 0%nat => nil
        | S l' => base :: (range (base + 1) l')
        end.

        Lemma length: forall l b, length (range b l) = l.
        Proof. induction l; intros b; cbn. - reflexivity. - rewrite -> IHl. reflexivity. Qed.

        Lemma indexing {F: Type} {f: Result.AssertionError F}: forall i b l v,
          Indexing.Int.indexing (range b l) i = Success v -> v = (b + i)%Z.
        Proof.
          destruct i as [ | p | p ].
          - intros. cbn in *.
            destruct l; try Result.assertion_failed_helper. cbn in *.
            injection H as [=->]. lia.
          - induction p using POrderedType.Positive_as_DT.peano_rect.
            + intros. cbn in H.
              destruct l; try Result.assertion_failed_helper. cbn in *.
              rewrite -> Pos2Nat.inj_1 in H.
              rewrite -> Indexing.Nat.cons in H.
              destruct l; try Result.assertion_failed_helper. cbn in *.
              injection H as [=->]. reflexivity.
            + intros. cbn in *. rewrite -> Pos2Nat.inj_succ in H.
              destruct l; try Result.assertion_failed_helper. cbn in *.
              specialize (IHp (b + 1)%Z l). cbn in IHp.
              rewrite -> Indexing.Nat.cons in H.
              specialize (IHp _ H). lia.
          - intros. cbn in H. Result.assertion_failed_helper.
        Qed.

        Lemma completeness {F: Type} {f: Result.AssertionError F}: forall s l z, (s <= z)%Z -> (z < s + Z.of_nat l)%Z -> exists i, Indexing.Int.indexing (range s l) i = Success z.
        Proof.
          intros. remember (z - s)%Z as i.
          exists i.
          assert (0 <= i < Z.of_nat l)%Z as Bounds by lia.
          rewrite <- length with (b := s) (l := l) in Bounds.
          destruct (Indexing.Int.indexing (range s l) i) eqn:Eq.
          - apply indexing in Eq. f_equal. lia.
          - apply Indexing.Int.failure_bounds in Eq. lia.
        Qed.
      End Length.

      Module Bounds.
        Definition range(from to: Z) := Length.range from ( Z.to_nat (to - from)%Z ).

        Lemma length: forall s e, length (range s e) = Z.to_nat (e - s)%Z.
        Proof. unfold range. intros. apply Length.length. Qed.

        Lemma indexing {F: Type} {f: Result.AssertionError F}: forall s e i v,
          Indexing.Int.indexing (range s e) i = Success v -> v = (s + i)%Z.
        Proof. unfold range. intros. apply Length.indexing with (1 := H). Qed.

        Lemma completeness {F: Type} {f: Result.AssertionError F}: forall s e z, (s <= z)%Z -> (z < e)%Z -> exists i, Indexing.Int.indexing (range s e) i = Success z.
        Proof. unfold range. intros. apply Length.completeness; lia. Qed.
      End Bounds.
    End Int.
  End Range.
End List.