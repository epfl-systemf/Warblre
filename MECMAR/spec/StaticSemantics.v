From Coq Require Import List.
From Warblre Require Import List Base Result Patterns Coercions.

Import Coercions.

Module StaticSemantics.

  Fixpoint pre_order_walk (r: Regex) (ctx: RegexContext): list (Regex * RegexContext) :=
    (r, ctx) ::
    match r with
    | Empty => nil
    | Char _ => nil
    | Dot => nil
    | CharacterClass _ => nil
    | AtomEsc _ => nil
    | Disjunction r1 r2 => pre_order_walk r1 (Disjunction_left r2 :: ctx) ++ pre_order_walk r2 (Disjunction_right r1 :: ctx)
    | Quantified r0 q => pre_order_walk r0 (Quantified_inner q :: ctx)
    | Seq r1 r2 => pre_order_walk r1 (Seq_left r2 :: ctx) ++ pre_order_walk r2 (Seq_right r1 :: ctx)
    | Group name r0 => pre_order_walk r0 (Group_inner name :: ctx)
    | Lookahead r0 => pre_order_walk r0 (Lookahead_inner :: ctx)
    | NegativeLookahead r0 => pre_order_walk r0 (NegativeLookahead_inner :: ctx)
    | Lookbehind r0 => pre_order_walk r0 (Lookbehind_inner :: ctx)
    | NegativeLookbehind r0 => pre_order_walk r0 (NegativeLookbehind_inner :: ctx)
    end.

  Lemma pre_order_walk_roots: forall r ctx i r' ctx', List.Indexing.Nat.indexing (pre_order_walk r ctx) i = Success (r', ctx') -> zip r ctx = zip r' ctx'.
  Proof.
    induction r; intros; cbn in *; (destruct i; [ intros; cbn in *; injection H as <- <-; reflexivity | rewrite -> List.Indexing.Nat.cons in H ]).
    + rewrite -> List.Indexing.Nat.nil in H. Result.assertion_failed_helper.
    + rewrite -> List.Indexing.Nat.nil in H. Result.assertion_failed_helper.
    + rewrite -> List.Indexing.Nat.nil in H. Result.assertion_failed_helper.
    + rewrite -> List.Indexing.Nat.nil in H. Result.assertion_failed_helper.
    + rewrite -> List.Indexing.Nat.nil in H. Result.assertion_failed_helper.
    + apply List.Indexing.Nat.concat in H as  [[ _ ? ]|[ _ ? ]].
      * symmetry in H. rewrite <- IHr1 with (1 := H). cbn. reflexivity.
      * symmetry in H. rewrite <- IHr2 with (1 := H). cbn. reflexivity.
    + rewrite <- IHr with (1 := H). cbn. reflexivity.
    + apply List.Indexing.Nat.concat in H as  [[ _ ? ]|[ _ ? ]].
      * symmetry in H. rewrite <- IHr1 with (1 := H). cbn. reflexivity.
      * symmetry in H. rewrite <- IHr2 with (1 := H). cbn. reflexivity.
    + rewrite <- IHr with (1 := H). cbn. reflexivity.
    + rewrite <- IHr with (1 := H). cbn. reflexivity.
    + rewrite <- IHr with (1 := H). cbn. reflexivity.
    + rewrite <- IHr with (1 := H). cbn. reflexivity.
    + rewrite <- IHr with (1 := H). cbn. reflexivity.
  Qed.

  (** 22.2.1.1 Static Semantics: Early Errors *)

  (** 22.2.1.2 Static Semantics: CountLeftCapturingParensWithin *)
  Fixpoint countLeftCapturingParensWithin_impl (r: Regex): non_neg_integer :=
    match r with
    | Empty => 0
    | Char _ => 0
    | Dot => 0
    | AtomEsc _ => 0
    | CharacterClass _ => 0
    | Disjunction r1 r2 => (countLeftCapturingParensWithin_impl r1) + (countLeftCapturingParensWithin_impl r2)
    | Quantified r0 _ => countLeftCapturingParensWithin_impl r0
    | Seq r1 r2 => (countLeftCapturingParensWithin_impl r1) + (countLeftCapturingParensWithin_impl r2)
    | Group _ r0 => 1 + (countLeftCapturingParensWithin_impl r0)
    | Lookahead r0 => countLeftCapturingParensWithin_impl r0
    | NegativeLookahead r0 => countLeftCapturingParensWithin_impl r0
    | Lookbehind r0 => countLeftCapturingParensWithin_impl r0
    | NegativeLookbehind r0 => countLeftCapturingParensWithin_impl r0
    end.
  Definition countLeftCapturingParensWithin (r: Regex) (ctx: RegexContext): non_neg_integer := countLeftCapturingParensWithin_impl r.

  (** 22.2.1.3 Static Semantics: CountLeftCapturingParensBefore *)
  Fixpoint countLeftCapturingParensBefore_impl (ctx: RegexContext): non_neg_integer :=
    match ctx with
    | nil => 0
    | h :: t => (countLeftCapturingParensBefore_impl t) + match h with
      | Disjunction_left _ => 0
      | Disjunction_right l => countLeftCapturingParensWithin_impl l
      | Quantified_inner _ => 0
      | Seq_left _ => 0
      | Seq_right l => countLeftCapturingParensWithin_impl l
      | Group_inner _ => 1
      | Lookahead_inner => 0
      | NegativeLookahead_inner => 0
      | Lookbehind_inner => 0
      | NegativeLookbehind_inner => 0
      end
    end.
  Definition countLeftCapturingParensBefore (r: Regex) (ctx: RegexContext): non_neg_integer := countLeftCapturingParensBefore_impl ctx.

  (** 22.2.1.4 Static Semantics: CapturingGroupNumber *)

  (** 22.2.1.5 Static Semantics: IsCharacterClass *)

  (** 22.2.1.6 Static Semantics: CharacterValue *)
  Definition characterValue {F: Type} {_: Result.AssertionError F} (self: ClassAtom): Result non_neg_integer F := match self with
  (** ClassAtomNoDash :: SourceCharacter *)
  | SourceCharacter chr =>
      (* 1. Let ch be the code point matched by SourceCharacter. *)
      (*+ TODO: What is that sentence supposed to mean ?!? *)
      let ch := chr in
      (* 2. Return the numeric value of ch. *)
      Character.numeric_value ch

  (** ClassEscape :: b *)
  | ClassEsc (ClassEscape.b) =>
      (* 1. Return the numeric value of U+0008 (BACKSPACE). *)
      Character.numeric_value Character.BACKSPACE

  (** ClassEscape :: - *)
  | ClassEsc (ClassEscape.Dash) =>
      (* 1. Return the numeric value of U+002D (HYPHEN-MINUS). *)
      Character.numeric_value Character.HYPHEN_MINUS

  (** CharacterEscape :: ControlEscape *)
  | ClassEsc (ClassEscape.CharacterEsc (CharacterEscape.ControlEsc esc)) =>
      (* 1. Return the numeric value according to Table 63. *)
      match esc with
      | ControlEscape.t => Character.numeric_value Character.CHARACTER_TABULATION
      | ControlEscape.n => Character.numeric_value Character.LINE_FEED
      | ControlEscape.v => Character.numeric_value Character.LINE_TABULATION
      | ControlEscape.f => Character.numeric_value Character.FORM_FEED
      | ControlEscape.r => Character.numeric_value Character.CARRIAGE_RETURN
      end

  (** CharacterEscape :: 0 *)
  | ClassEsc (ClassEscape.CharacterEsc (CharacterEscape.Zero)) =>
      (* 1. Return the MV of HexEscapeSequence. *)
      Character.numeric_value Character.NULL

  (** CharacterEscape :: IdentityEscape *)
  | ClassEsc (ClassEscape.CharacterEsc (CharacterEscape.IdentityEsc chr)) =>
      (* 1. Let ch be the code point matched by IdentityEscape. *)
      let ch := chr in
      (* 2. Return the numeric value of ch. *)
      Character.numeric_value ch

  | _ => Result.assertion_failed
  end.

  (** 22.2.1.7 Static Semantics: GroupSpecifiersThatMatch ( thisGroupName ) *)
  Definition groupSpecifiersThatMatch (r: Regex) (ctx: RegexContext) (thisGroupName: GroupName): list (Regex * RegexContext) :=
    (* 1. Let name be the CapturingGroupName of thisGroupName. *)
    let name := thisGroupName in
    (* 2. Let pattern be the Pattern containing thisGroupName. *)
    let pattern := zip r ctx in
    (* 3. Let result be a new empty List. *)
    (* 4. For each GroupSpecifier gs that pattern contains, do *)
    let result := List.flat_map ( fun r => match r with
      | (Group (Some gs) inner, ctx) =>
        (* a. If the CapturingGroupName of gs is name, then *)
        if (GroupName.eqs gs name) then
          (* i. Append gs to result. *)
          (inner, Group_inner (Some gs) :: ctx) :: nil
        else nil
      | _ => nil
      end
      ) (pre_order_walk pattern nil)
    in
    (* 5. Return result. *)
    result.

  (** 22.2.1.8 Static Semantics: CapturingGroupName *)

  (** 22.2.1.9 Static Semantics: RegExpIdentifierCodePoints *)

  (** 22.2.1.10 Static Semantics: RegExpIdentifierCodePoint *)
End StaticSemantics.
Export StaticSemantics.
