From Warblre Require Import API.
From Warblre Require Import Frontend.
From Stdlib Require Import Lia.

(* This is one instantiation of the alphabet that can be executed within Rocq. *)
(* This encodes the ASCII alphabet *)

(* TODOs:

   - Merge CharSetExt into CharSet.
     Use MSet API + a few functions / proofs.
   - Update NaiveEngineParameters with new functions.
   - Linden: instantiate and test
   - Keep just one of FastEngine and NaiveEngine
 *)

Module NaiveEngineParameters <: API.EngineParameters.
  Import RegExpRecord Numeric List PeanoNat Result.
  Import List.ListNotations.
  Open Scope list_scope.

  Definition character : Type := nat.

  Module Character.
    Definition equal: forall (l r: character), {l=r} + {l<>r} :=
      Nat.eq_dec.
    Definition from_numeric_value (n: nat): character :=
      n.
    Definition numeric_value (c: character) : nat :=
      c.

    (* ascii-specific canonicalization *)
    Definition canonicalize (r: RegExpRecord) (ch: character): character :=
      match (RegExpRecord.ignoreCase r) with
      | true =>
          (* following https://unicode.org/Public/UCD/latest/ucd/CaseFolding.txt *)
          match ch with
          | 0x0041 => 0x0061
          | 0x0042 => 0x0062
          | 0x0043 => 0x0063
          | 0x0044 => 0x0064
          | 0x0045 => 0x0065
          | 0x0046 => 0x0066
          | 0x0047 => 0x0067
          | 0x0048 => 0x0068
          | 0x0049 => 0x0069
          | 0x004A => 0x006A
          | 0x004B => 0x006B
          | 0x004C => 0x006C
          | 0x004D => 0x006D
          | 0x004E => 0x006E
          | 0x004F => 0x006F
          | 0x0050 => 0x0070
          | 0x0051 => 0x0071
          | 0x0052 => 0x0072
          | 0x0053 => 0x0073
          | 0x0054 => 0x0074
          | 0x0055 => 0x0075
          | 0x0056 => 0x0076
          | 0x0057 => 0x0077
          | 0x0058 => 0x0078
          | 0x0059 => 0x0079
          | 0x005A => 0x007A
          | _ => ch
          end
      | false => ch
      end.

    Theorem numeric_pseudo_bij: forall c, from_numeric_value (numeric_value c) = c.
    Proof. reflexivity. Qed.

    Theorem numeric_round_trip_order: forall l r, l <= r -> (numeric_value (from_numeric_value l)) <= (numeric_value (from_numeric_value r)).
    Proof. easy. Qed.

    Theorem canonicalize_casesenst: forall rer chr, RegExpRecord.ignoreCase rer = false -> canonicalize rer chr = chr.
    Proof. intros rer chr H. unfold canonicalize. rewrite H. auto. Qed.

  End Character.

  Definition string : Type :=
    list character.

  Module String.
    Definition equal: forall (l r: string), {l=r} + {l<>r}.
    Proof.
      decide equality.
      eauto using Character.equal.
    Defined.
    Definition length (str: string) : non_neg_integer :=
      List.length str.
    Definition substring (str: string) (s: non_neg_integer) (e: non_neg_integer) : string :=
      List.take (List.drop str s) (e - s).
    Definition advanceStringIndex (str: string) (i: non_neg_integer) : non_neg_integer :=
      S i.
    Definition getStringIndex (str: string) (i: non_neg_integer) : non_neg_integer :=
      i.
    Definition list_from_string (str: string) : list character :=
      str.
    Definition list_to_string (l: list character) : string :=
      l.
  End String.

  Definition char_set: Type := ListSet.set character.

  Module CharSet.
    Definition empty: char_set := ListSet.empty_set character.
    Definition from_list (l: list character) : char_set := List.nodup Character.equal l.
    Definition union (cs0 cs1: char_set) : char_set := ListSet.set_union Character.equal cs0 cs1.
    Definition singleton (c: character) : char_set := [c].
    Definition size (cs: char_set) : nat := List.length (List.nodup Character.equal cs).
    Definition remove_all (l r: char_set) : char_set := ListSet.set_diff Character.equal l r.
    Definition is_empty (cs: char_set) : bool := size cs =? 0.
    Definition elements (cs: char_set): list character := List.nodup Character.equal cs.
    Definition contains (cs: char_set) (c: character) : bool := ListSet.set_mem Character.equal c cs.
    Definition range (first: character) (last: character) : char_set :=
      List.Range.Nat.Bounds.range first (last + 1).
    Definition unique (F: Type) (_: Result.AssertionError F) (cs: char_set) : Result character F :=
      match List.nodup Character.equal cs with
      | [x] => Result.Success x (* Assumes deduplicated ListSet *)
      | _ => Result.assertion_failed
      end.
    Definition filter (cs: char_set) (f: character -> bool) : char_set :=
      List.filter f cs.
    Definition exist (cs: char_set) (f: character -> bool) : bool :=
      List.existsb f cs.
    Definition exist_canonicalized (rer: RegExpRecord) (cs: char_set) (c: character): bool :=
      contains (List.map (Character.canonicalize rer) cs) c.

    (*Theorem singleton_size: forall c, size (singleton c) = 1.
    Proof. reflexivity. Qed.
    Theorem singleton_exist: forall c p, exist (singleton c) p = p c.
    Proof. cbv; destruct p; reflexivity. Qed.
    Theorem singleton_unique: forall (F: Type) (af: Result.AssertionError F) c, @unique F af (singleton c) = Success c.
    Proof. reflexivity. Qed.*)
    Theorem exist_canonicalized_equiv rer cs c :
      exist_canonicalized rer cs c =
        exist
          cs
          (fun c0 =>
             if Character.equal (Character.canonicalize rer c0) c
             then true else false).
    Proof.
      induction cs; simpl.
      - reflexivity.
      - unfold exist_canonicalized in *.
        simpl.
        repeat destruct Character.equal.
        all: reflexivity || assumption || congruence.
    Qed.
    Definition In : character -> char_set -> Prop := @ListSet.set_In character.
    Definition Equal s1 s2 := forall c, In c s1 <-> In c s2.
    Definition Empty s := forall c, ~In c s.
    Definition Exists (P: character -> Prop) s := exists c, In c s /\ P c.
    Theorem empty_spec: forall c, ~In c empty.
    Proof. intros c []. Qed.
    Theorem from_list_spec: forall c l, In c (from_list l) <-> List.In c l.
    Proof.
      intros c l. unfold from_list, In, ListSet.set_In.
      apply List.nodup_In.
    Qed.
    Theorem union_spec: forall c s1 s2, In c (union s1 s2) <-> In c s1 \/ In c s2.
    Proof. apply ListSet.set_union_iff. Qed.
    Theorem singleton_spec: forall x c, In x (singleton c) <-> c = x.
    Proof.
      intros x c. split.
      - intros []; auto. inversion H.
      - intros ->. left. reflexivity.
    Qed.
    Theorem size_spec: forall s, size s = List.length (elements s).
    Proof. reflexivity. Qed.
    Theorem remove_all_spec: forall c s1 s2, In c (remove_all s1 s2) <-> In c s1 /\ ~In c s2.
    Proof. apply ListSet.set_diff_iff. Qed.
    Theorem is_empty_spec: forall s, is_empty s = true <-> Empty s.
    Proof.
      intro s. unfold is_empty, size.
      split.
      - rewrite Nat.eqb_eq. intros H x IN. apply <- (List.nodup_In Character.equal) in IN.
        apply List.length_zero_iff_nil in H. rewrite H in IN. destruct IN.
      - unfold Empty. intro NOTHING. destruct (List.nodup Character.equal s) eqn:Heqnodups; try reflexivity.
        exfalso. apply NOTHING with (c := c). apply (List.nodup_In Character.equal).
        rewrite Heqnodups. left. reflexivity.
    Qed.
    Theorem contains_spec: forall c s, contains s c = true <-> In c s.
    Proof.
      intros c s. split; intro H.
      - apply ListSet.set_mem_correct1 with (Aeq_dec := Character.equal). auto.
      - apply ListSet.set_mem_correct2 with (Aeq_dec := Character.equal). auto.
    Qed.

    Lemma range_seq: forall base l, List.List.Range.Nat.Length.range base l = Stdlib.Lists.List.seq base l.
    Proof.
      intros base l.
      revert base.
      induction l as [|l IHl].
      - simpl. reflexivity.
      - intro base. simpl. f_equal. replace (base + 1)%nat with (S base) by lia.
        apply IHl.
    Qed.

    (* TODO copied from Linden; should be somewhere else*)
    Theorem range_spec: forall c l h, In c (range l h) <-> Character.numeric_value l <= Character.numeric_value c /\ Character.numeric_value c <= Character.numeric_value h.
    Proof.
      intros c l h. unfold range, List.Range.Nat.Bounds.range.
      rewrite range_seq, List.in_seq. unfold Character.numeric_value. lia.
    Qed.

    Lemma Equal_singleton_nodup:
      forall s c, Equal s (singleton c) <-> List.nodup Character.equal s = [c].
    Proof.
      intros s c. induction s.
      - simpl. split; intro H.
        + exfalso. specialize (H c) as [Hl Hr]. apply Hr. left. reflexivity.
        + discriminate H.
      - destruct s as [|b s].
        + unfold singleton. simpl. split; intro H.
          * f_equal. specialize (H a) as [Hl Hr]. specialize (Hl (or_introl eq_refl)).
            destruct Hl; [auto|contradiction].
          * inversion H. subst. intro c0. split; auto.
        + split.
          * intro EQUAL.
            replace a with c in *. 2: {
              specialize (EQUAL a) as [EQUALl EQUALr].
              specialize (EQUALl (or_introl eq_refl)).
              destruct EQUALl; [auto|contradiction].
            }
            replace b with c in *. 2: {
              specialize (EQUAL b) as [EQUALl EQUALr].
              specialize (EQUALl (or_intror (or_introl eq_refl))).
              destruct EQUALl; [auto|contradiction].
            }
            assert (Equal (c::s) (singleton c)). {
              intro c0. split; intro H.
              - apply EQUAL. right. auto.
              - destruct H; [|inversion H]. subst c0. left. reflexivity.
            }
            remember (c::s) as s'. simpl.
            destruct (List.in_dec Character.equal c s').
            2: { exfalso. apply n. rewrite Heqs'. left. reflexivity. }
            apply IHs. auto.
          * remember (b::s) as s'. simpl.
            destruct List.in_dec.
            -- intro H. rewrite <- IHs in H.
               intro c0. split; intro.
               ++ destruct H0.
                  ** subst c0. specialize (proj1 (H a) i). auto.
                  ** apply H. auto.
               ++ right. apply H. auto.
            -- destruct List.nodup eqn:?. 2: discriminate.
               replace s' with (@nil character). 2: {
                 symmetry.
                 assert (forall c0, ~List.In c0 s'). {
                   intro c0. rewrite <- List.nodup_In with (decA := Character.equal), Heql.
                   apply List.in_nil.
                 }
                 destruct s'; auto. exfalso. apply (H c0). left. reflexivity.
               }
               intro H. inversion H. subst.
               intro c0. split; auto.
    Qed.


    Theorem unique_succ_spec: forall (F: Type) (H: Result.AssertionError F) (c: character) (s: char_set),
      unique F H s = Success c <-> Equal s (singleton c).
    Proof.
      intros F H c s. split.
      - unfold unique, Result.assertion_failed. destruct H.
        destruct List.nodup eqn:?; try discriminate.
        destruct l; try discriminate.
        intro H. injection H as ->. apply Equal_singleton_nodup. auto.
      - intro H0. unfold unique. apply Equal_singleton_nodup in H0. rewrite H0. reflexivity.
    Qed.
    Theorem unique_succ_error: forall (F: Type) (H: Result.AssertionError F) (s: char_set),
      (exists c, unique F H s = Success c) \/ unique F H s = Error (@Result.f F H).
    Proof.
      intros F H s. unfold unique.
      destruct List.nodup.
      - right. unfold Result.assertion_failed, Result.f. destruct H. reflexivity.
      - destruct l. + left. eexists. reflexivity. +  right. unfold Result.assertion_failed, Result.f. destruct H. reflexivity.
    Qed.
    Theorem filter_spec: forall f c s,
      In c (filter s f) <-> In c s /\ f c = true.
    Proof. apply List.filter_In. Qed.
    Theorem exist_spec: forall f s,
      exist s f = true <-> Exists (fun c => f c = true) s.
    Proof. apply List.existsb_exists. Qed.
    Theorem elements_spec1: forall c s, List.In c (elements s) <-> In c s.
    Proof. intros c s. apply List.nodup_In. Qed.
    Theorem elements_spec2: forall s, List.NoDup (elements s).
    Proof. intros s. apply List.NoDup_nodup. Qed.

    Lemma union_empty_actual s: union s empty = s.
    Proof. reflexivity. Qed.

    Lemma Empty_empty s: Empty s -> s = CharSet.empty.
    Proof.
      destruct s.
      - reflexivity.
      - intro H. exfalso. unfold Empty in H. exact (H c (or_introl eq_refl)).
    Qed.

    Theorem union_empty: forall s e, Empty e -> union s e = s.
    Proof.
      intros; rewrite (Empty_empty e) by assumption.
      reflexivity.
    Qed.
  End CharSet.

  Module CharSets.
    Definition all: list character :=
      Eval cbv in List.Range.Nat.Bounds.range 0 0x80.
    Definition line_terminators: list character := [
        (* line feed *) 0xA;
        (* vertical tab *) 0xB;
        (* form feed *) 0xC;
        (* carriage return *) 0xD
      ].
    Definition digits: list character :=
      Eval cbv in List.Range.Nat.Bounds.range 0x30 0x3A.
    Definition white_spaces: list character := [
        (* line feed *) 0x0A;
        (* line tabulation *) 0x0B;
        (* form feed *) 0x0C;
        (* carriage return *) 0x0D;
        (* space *) 0x20
      ].
    Definition ascii_word_characters: list character :=
      Eval cbv in (
          (List.Range.Nat.Bounds.range 65 91) ++ (* uppercase *)
            (List.Range.Nat.Bounds.range 97 123) ++ (* lowercase *)
            (List.Range.Nat.Bounds.range 48 58) ++ (* numbers *)
            [95] (* '_' *)
        ).
  End CharSets.

  Definition property: Type := list character.
  Module Property.
    Definition equal: forall (l r: property), {l=r} + {l<>r}.
    Proof.
      decide equality; eauto using Character.equal.
    Defined.
    Definition code_points (p: property) : list character :=
      p.
  End Property.
End NaiveEngineParameters.


(* We remove the fast engine, at least for now *)

(*
From Stdlib Require Import OrdersEx MSetRBT.

Module FastEngineParameters <: API.EngineParameters.
  Import RegExpRecord Numeric List ZArith Result.
  Import List.ListNotations.
  Open Scope list_scope.
  Open Scope N_scope.

  Definition character : Type := N.

  Module Character.
    Definition equal: forall (l r: character), {l=r} + {l<>r} :=
      N.eq_dec.
    Definition from_numeric_value (n: nat): character :=
      N.of_nat n.
    Definition numeric_value (c: character) : nat :=
      N.to_nat c.
    (* TODO: This naive implementation does not canonicalize. *)
    Definition canonicalize (r: RegExpRecord) (c: character): character :=
      c.

    Theorem numeric_pseudo_bij: forall c, from_numeric_value (numeric_value c) = c.
    Proof. apply Nnat.N2Nat.id. Qed.

    Theorem numeric_round_trip_order: forall l r,
        (l <= r)%nat ->
        (numeric_value (from_numeric_value l) <= numeric_value (from_numeric_value r))%nat.
    Proof.
      unfold numeric_value, from_numeric_value; intros; rewrite !Nnat.Nat2N.id.
      assumption.
    Qed.
  End Character.

  Definition string : Type :=
    list character.

  Module String.
    Definition equal: forall (l r: string), {l=r} + {l<>r}.
    Proof.
      decide equality.
      eauto using Character.equal.
    Defined.
    Definition length (str: string) : non_neg_integer :=
      List.length str.
    Definition substring (str: string) (s: non_neg_integer) (e: non_neg_integer) : string :=
      List.take (List.drop str s) (e - s).
    Definition advanceStringIndex (str: string) (i: non_neg_integer) : non_neg_integer :=
      S i.
    Definition getStringIndex (str: string) (i: non_neg_integer) : non_neg_integer :=
      i.
    Definition list_from_string (str: string) : list character :=
      str.
    Definition list_to_string (l: list character) : string :=
      l.
  End String.

  Module RBT := MSetRBT.Make OrdersEx.N_as_OT.
  Module CS := RBT.Raw.
  Definition char_set: Type := CS.t.

  Module CharSet.
    Definition empty: char_set := CS.empty.
    Definition from_list (l: list character) : char_set :=
      List.fold_left (fun cs c => CS.add c cs) l CS.empty.
    Definition union (cs0 cs1: char_set) : char_set :=
      CS.union cs0 cs1.
    Definition singleton (c: character) : char_set :=
      CS.singleton c.
    Definition size (cs: char_set) : nat :=
      CS.cardinal cs.
    Definition remove_all (l r: char_set) : char_set :=
      CS.diff l r.
    Definition is_empty (cs: char_set) : bool :=
      CS.is_empty cs.
    Definition elements (cs: char_set): list character :=
      CS.elements cs.
    Definition contains (cs: char_set) (c: character) : bool :=
      CS.mem c cs.
    Definition range (first: character) (last: character) : char_set :=
      N.peano_rect
        (fun _ => CS.t) CS.empty (fun d cs => CS.add (first + d) cs)
        (N.succ last - first).
    Definition unique (F: Type) (_: Result.AssertionError F) (cs: char_set) : Result character F :=
      match cs with
      | CS.Leaf => Result.assertion_failed
      | CS.Node _ _ c _ => Result.Success c
      end.
    Definition filter (cs: char_set) (f: character -> bool) : char_set :=
      CS.filter f cs.
    Definition exist (cs: char_set) (f: character -> bool) : bool :=
      CS.exists_ f cs.
    Definition exist_canonicalized (rer: RegExpRecord) (cs: char_set) (c: character): bool :=
      exist
        cs
        (fun c0 =>
           if Character.equal (Character.canonicalize rer c0) c
           then true else false).
    (*Theorem singleton_size: forall c, size (singleton c) = 1%nat.
    Proof. reflexivity. Qed.
    Theorem singleton_exist: forall c p, exist (singleton c) p = p c.
    Proof. cbv; destruct p; reflexivity. Qed.
    Theorem singleton_unique: forall (F: Type) (af: Result.AssertionError F) c, @unique F af (singleton c) = Success c.
    Proof. reflexivity. Qed.*)
    Theorem exist_canonicalized_equiv rer cs c :
      exist_canonicalized rer cs c =
        exist
          cs
          (fun c0 =>
             if Character.equal (Character.canonicalize rer c0) c
             then true else false).
    Proof.
      reflexivity.
    Qed.

    Definition In: character -> char_set -> Prop := CS.In.
    Definition Equal s1 s2 := forall c, In c s1 <-> In c s2.
    Definition Empty s := forall c, ~In c s.
    Definition Exists (P: character -> Prop) s := exists c, In c s /\ P c.

    Theorem empty_spec: forall c, ~ In c empty.
    Proof. apply CS.empty_spec. Qed.
    Theorem from_list_spec: forall c l, In c (from_list l) <-> List.In c l.
    Proof. Admitted.
    Theorem union_spec: forall c s1 s2, In c (union s1 s2) <-> In c s1 \/ In c s2.
    Proof. intros c s1 s2. apply CS.union_spec. Print CS.t.
    Admitted.
  End CharSet.

  Module CharSets.
    Definition N_range first last :=
      List.rev
        (N.peano_rect
           (fun _ => list N) [] (fun d cs => (first + d)%N :: cs)
           (N.succ last - first)%N).
    Definition all: list character :=
      Eval cbv in N_range 0 0x80.
    Definition line_terminators: list character := [
        (* line feed *) 0xA;
        (* vertical tab *) 0xB;
        (* form feed *) 0xC;
        (* carriage return *) 0xD
      ].
    Definition digits: list character :=
      Eval cbv in N_range 0x30 0x3A.
    Definition white_spaces: list character := [
        (* line feed *) 0x0A;
        (* line tabulation *) 0x0B;
        (* form feed *) 0x0C;
        (* carriage return *) 0x0D;
        (* space *) 0x20
      ].
    Definition ascii_word_characters: list character :=
      Eval cbv in (
          (N_range 65 91) ++ (* uppercase *)
            (N_range 97 123) ++ (* lowercase *)
            (N_range 48 58) ++ (* numbers *)
            [95] (* '_' *)
        ).
  End CharSets.

  Definition property: Type := list character.
  Module Property.
    Definition equal: forall (l r: property), {l=r} + {l<>r}.
    Proof.
      decide equality; eauto using Character.equal.
    Defined.
    Definition code_points (p: property) : list character :=
      p.
  End Property.
End FastEngineParameters.
*)

Module NaiveEngine := API.Engine (NaiveEngineParameters).
(*Module FastEngine := API.Engine (NaiveEngineParameters).*)

Require Import Stdlib.Strings.Ascii Stdlib.Strings.String.
Open Scope string_scope.

Import API.Patterns Result.
Import List.ListNotations.
Open Scope list_scope.
Import NaiveEngine.
(* Import FastEngine. *)

Definition get_success {S F: Type} (r: Result S F) : match r with Success _ => S | Error _ => unit end :=
  match r with
  | Success s => s
  | Error f => tt
  end.

Definition string_of_String (s: Stdlib.Strings.String.string) :=
  List.map Byte.to_nat (String.list_byte_of_string s).

Definition character_of_Ascii (a: Stdlib.Strings.Ascii.ascii) :=
  Byte.to_nat (byte_of_ascii a).

Example flags :=
  (RegExpFlags.make false false false false false tt false).

Notation "! r" := (get_success (initialize r flags)) (at level 9).
Notation "$ c" := (character_of_Ascii c) (at level 9).
Notation "$$ s" := (string_of_String s) (at level 9).

(* Hide the matching functions in the outputs below*)
Arguments Exotic {C S UP}%_type_scope {H H0 H1} _ {_}.
Arguments Null {C S UP}%_type_scope {H H0 H1} {_}.

(*
Time Compute
  rmatch
    ! (Char $ "l")
    $$ "hello".

Time Compute
  rmatch
    ! (Char $ "z")
    $$ "hello".

Time Compute
  rmatch
    ! (Quantified (Char $ "l") (Greedy Plus))
    $$ "hello".

Time Compute
  rmatch
    ! (Quantified
         (Seq
            (Quantified (Char $ "a") (Greedy Question))
            (Quantified (Char $ "b") (Lazy Question)))
         (Greedy Star))
    $$ "ab".

Time Compute
  rmatch
    ! (Quantified
         (Group
            None
            (Seq
               (Quantified (Char $ "a") (Greedy Question))
               (Quantified (Char $ "b") (Lazy Question))))
         (Greedy Star))
    $$ "ab". *)
