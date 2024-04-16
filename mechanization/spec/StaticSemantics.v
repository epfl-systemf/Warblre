From Coq Require Import PeanoNat List Bool.
From Warblre Require Import Result List Base Result Patterns Node Characters Coercions Typeclasses.

Import Coercions.
Import Result.Notations.
Import Result.Notations.Boolean.
Local Open Scope result_flow.

Section StaticSemantics.
  Context {Character} `{ep: CharacterInstance Character}.
  Import Patterns.

  (** 22.2.1.9 Static Semantics: RegExpIdentifierCodePoints *)

  (** 22.2.1.10 Static Semantics: RegExpIdentifierCodePoint *)

  (** 22.2.1.8 Static Semantics: CapturingGroupName *)
  Definition capturingGroupName (gn: GroupName): GroupName := gn.

  (** 22.2.1.7 Static Semantics: GroupSpecifiersThatMatch ( thisGroupName ) *)
  Definition groupSpecifiersThatMatch (r: Regex) (ctx: RegexContext) (thisGroupName: GroupName): list (Regex * RegexContext) :=
    (* 1. Let name be the CapturingGroupName of thisGroupName. *)
    let name := capturingGroupName thisGroupName in
    (* 2. Let pattern be the Pattern containing thisGroupName. *)
    let pattern := zip r ctx in
    (* 3. Let result be a new empty List. *)
    (* 4. For each GroupSpecifier gs that pattern contains, do *)
    let result := List.flat_map ( fun r => match r with
      | (Group (Some gs) inner, ctx) =>
        (* a. If the CapturingGroupName of gs is name, then *)
        if (gs =?= name) then
          (* i. Append gs to result. *)
          (inner, Group_inner (Some gs) :: ctx) :: nil
        else nil
      | _ => nil
      end
      ) (Zipper.Walk.walk pattern nil)
    in
    (* 5. Return result. *)
    result.

  (** 22.2.1.6 Static Semantics: CharacterValue *)
  Definition characterValue_Hex4Digits (self: Hex4Digits): non_neg_integer :=
    (** HexLeadSurrogate :: Hex4Digits *)
    (** HexTrailSurrogate :: Hex4Digits *)
    (** HexNonSurrogate :: Hex4Digits *)
    (* Return the MV of Hex4Digits. *)
    HexDigit.to_integer_4 self.

  Definition characterValue {F: Type} {_: Result.AssertionError F} (self: ClassAtom): Result non_neg_integer F := match self with
  (** ClassAtomNoDash :: SourceCharacter *)
  | SourceCharacter chr =>
      (* 1. Let ch be the code point matched by SourceCharacter. *)
      (*+ TODO: What is that sentence supposed to mean ?!? *)
      let ch := chr in
      (* 2. Return the numeric value of ch. *)
      Character.numeric_value ch

  (** ClassEscape :: b *)
  | ClassEsc (esc_b) =>
      (* 1. Return the numeric value of U+0008 (BACKSPACE). *)
      Character.numeric_value Characters.BACKSPACE

  (** ClassEscape :: - *)
  | ClassEsc (esc_Dash) =>
      (* 1. Return the numeric value of U+002D (HYPHEN-MINUS). *)
      Character.numeric_value Characters.HYPHEN_MINUS

  (** CharacterEscape :: ControlEscape *)
  | ClassEsc (CCharacterEsc (ControlEsc esc)) =>
      (* 1. Return the numeric value according to Table 63. *)
      match esc with
      | esc_t => Character.numeric_value Characters.CHARACTER_TABULATION
      | esc_n => Character.numeric_value Characters.LINE_FEED
      | esc_v => Character.numeric_value Characters.LINE_TABULATION
      | esc_f => Character.numeric_value Characters.FORM_FEED
      | esc_r => Character.numeric_value Characters.CARRIAGE_RETURN
      end

  (** CharacterEscape :: c AsciiLetter *)
  | ClassEsc (CCharacterEsc (AsciiControlEsc l)) =>
      (* 1. Let ch be the code point matched by AsciiLetter. *)
      (* 2. Let i be the numeric value of ch. *)
      let i := AsciiLetter.numeric_value l in
      (* 3. Return the remainder of dividing i by 32. *)
      NonNegInt.modulo i 32

  (** CharacterEscape :: 0 *)
  | ClassEsc (CCharacterEsc (esc_Zero)) =>
      (* 1. Return the numeric value of U+0000 (NULL). *)
      Character.numeric_value Characters.NULL

  (** CharacterEscape :: HexEscapeSequence *)
  | ClassEsc (CCharacterEsc (HexEscape d1 d2)) =>
      (* 1. Return the MV of HexEscapeSequence. *)
      HexDigit.to_integer (d1 :: d2 :: nil)

  (** CharacterEscape :: IdentityEscape *)
  | ClassEsc (CCharacterEsc (IdentityEsc chr)) =>
      (* 1. Let ch be the code point matched by IdentityEscape. *)
      let ch := chr in
      (* 2. Return the numeric value of ch. *)
      Character.numeric_value ch

  (** RegExpUnicodeEscapeSequence :: u HexLeadSurrogate \u HexTrailSurrogate *)
  | ClassEsc (CCharacterEsc (UnicodeEsc (Pair head tail))) =>
    (* 1. Let lead be the CharacterValue of HexLeadSurrogate. *)
    let lead := characterValue_Hex4Digits head in
    (* 2. Let trail be the CharacterValue of HexTrailSurrogate. *)
    let trail := characterValue_Hex4Digits tail in
    (* 3. Let cp be UTF16SurrogatePairToCodePoint(lead, trail). *)
    let cp := Unicode.utf16SurrogatePair lead trail in
    (* 4. Return the numeric value of cp. *)
    cp

  (** RegExpUnicodeEscapeSequence :: u Hex4Digits *)
  | ClassEsc (CCharacterEsc (UnicodeEsc (Lonely hex))) =>
    (* 1. Return the MV of Hex4Digits. *)
    characterValue_Hex4Digits hex

  (** RegExpUnicodeEscapeSequence :: u{ CodePoint } *)
  | ClassEsc (CCharacterEsc (UnicodeEsc (CodePoint c))) => 
    (* Return the MV of CodePoint. *)
    Character.numeric_value c

  | ClassEsc (CCharacterClassEsc esc) => match esc with
    | esc_d => Result.assertion_failed
    | esc_D => Result.assertion_failed
    | esc_s => Result.assertion_failed
    | esc_S => Result.assertion_failed
    | esc_w => Result.assertion_failed
    | esc_W => Result.assertion_failed
    | UnicodeProp _ => Result.assertion_failed
    | UnicodePropNeg _ => Result.assertion_failed
    end
  end.

  (** 22.2.1.5 Static Semantics: IsCharacterClass *)
  Definition isCharacterClass (ca: ClassAtom): bool := match ca with
  (** ClassAtom ::
      -
      ClassAtomNoDash ::
      SourceCharacter but not one of \ or ] or -
      ClassEscape ::
      b
      -
      CharacterEscape *)
  | SourceCharacter _
  | ClassEsc (esc_b)
  | ClassEsc (esc_Dash)
  | ClassEsc (CCharacterEsc _) =>
      (* 1. Return false. *)
      false
  (** ClassEscape :: CharacterClassEscape *)
  | ClassEsc (CCharacterClassEsc _) =>
      (* 1. Return true. *)
      true
  end.

  (** 22.2.1.4 Static Semantics: CapturingGroupNumber *)
  Definition capturingGroupNumber (n: positive_integer): positive_integer := n.

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
    | InputStart => 0
    | InputEnd => 0
    | WordBoundary => 0
    | NotWordBoundary => 0
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

  (** 22.2.1.1 Static Semantics: Early Errors *)
  Fixpoint earlyErrors_class_ranges (cr: ClassRanges): Result bool SyntaxError := match cr with
  | EmptyCR => false
  | ClassAtomCR _ t => earlyErrors_class_ranges t
  (**  NonemptyClassRanges :: ClassAtom - ClassAtom ClassRanges *)
  | RangeCR l h t =>
      (* * It is a Syntax Error if IsCharacterClass of the first ClassAtom is true or IsCharacterClass of the second ClassAtom is true. *)
      if (isCharacterClass l is true) || (isCharacterClass h is true) then true
      (* * It is a Syntax Error if IsCharacterClass of the first ClassAtom is false, IsCharacterClass of the second ClassAtom is false, and the CharacterValue of the first ClassAtom is strictly greater than the CharacterValue of the second ClassAtom.  *)
      else if!
          Success (isCharacterClass l is false) &&!
          Success (isCharacterClass h is false) &&!
          (let! cvl =<< characterValue l in let! cvr =<< characterValue h in cvl >? cvr)%nat
        then true
      else earlyErrors_class_ranges t
  end.
  Definition earlyErrors_char_class (cc: CharClass): Result bool SyntaxError := match cc with
  | NoninvertedCC cr => earlyErrors_class_ranges cr
  | InvertedCC cr => earlyErrors_class_ranges cr
  end.

  Definition earlyErrors_quantifier_prefix (q: QuantifierPrefix): bool := match q with
  (**  QuantifierPrefix :: { DecimalDigits , DecimalDigits } *)
  | RepRange l h =>
      (* * It is a Syntax Error if the MV of the first DecimalDigits is strictly greater than the MV of the second DecimalDigits. *)
      if (l >? h)%nat then true else false
  | _ => false
  end.

  Definition earlyErrors_quantifier (q: Quantifier): bool := match q with
  | Lazy q => earlyErrors_quantifier_prefix q
  | Greedy q => earlyErrors_quantifier_prefix q
  end.

  Fixpoint earlyErrors_rec (r: Regex) (ctx: RegexContext): Result bool SyntaxError := match r with
    | Empty => false
    | Char _ => false
    | Dot => false
    (**  AtomEscape :: DecimalEscape *)
    | AtomEsc (DecimalEsc n) =>
        (* * It is a Syntax Error if the CapturingGroupNumber of DecimalEscape is strictly greater than CountLeftCapturingParensWithin(the Pattern containing AtomEscape). *)
        if (capturingGroupNumber n >? countLeftCapturingParensWithin (zip r ctx) nil)%nat then true else false
    (**  AtomEscape :: k GroupName *)
    | AtomEsc (GroupEsc name) =>
        (* * It is a Syntax Error if GroupSpecifiersThatMatch(GroupName) is empty. *)
        if (List.length (groupSpecifiersThatMatch (AtomEsc (GroupEsc name)) ctx name) =? 0)%nat then true else false
    | AtomEsc _ => false
    | CharacterClass cc => earlyErrors_char_class cc
    | Disjunction r1 r2 => earlyErrors_rec r1 (Disjunction_left r2 :: ctx) ||! earlyErrors_rec r2 (Disjunction_right r1 :: ctx)
    | Quantified r q => earlyErrors_rec r (Quantified_inner q :: ctx) ||! earlyErrors_quantifier q
    | Seq r1 r2 => earlyErrors_rec r1 (Seq_left r2 :: ctx) ||! earlyErrors_rec r2 (Seq_right r1 :: ctx)
    | Group name r => earlyErrors_rec r (Group_inner name :: ctx)
    | InputStart => false
    | InputEnd => false
    | WordBoundary => false
    | NotWordBoundary => false
    | Lookahead r => earlyErrors_rec r (Lookahead_inner :: ctx)
    | NegativeLookahead r => earlyErrors_rec r (NegativeLookahead_inner :: ctx)
    | Lookbehind r => earlyErrors_rec r (Lookbehind_inner :: ctx)
    | NegativeLookbehind r => earlyErrors_rec r (NegativeLookbehind_inner :: ctx)
    end.

  Definition earlyErrors (r: Regex) (ctx: RegexContext): Result bool SyntaxError :=
    let nodes := Zipper.Walk.walk r ctx in
    (**  Pattern :: Disjunction *)
    (* * It is a Syntax Error if CountLeftCapturingParensWithin(Pattern) ≥ 2^32 - 1. *)
    (* if (countLeftCapturingParensWithin r nil >=? 4294967295)%nat then true *)
    (* * It is a Syntax Error if Pattern contains two or more GroupSpecifiers for which CapturingGroupName of GroupSpecifier is the same. *)
    if! List.Exists.exist nodes (fun node0 =>
      List.Exists.exist nodes (fun node1 =>
        if node0 =?= node1 then false
        else
          let (r0, ctx0) := node0 in
          let (r1, ctx1) := node1 in
          match r0, r1 with
          | Group (Some name0) _, Group (Some name1) _ => name0 == name1
          | _, _ => false
          end
    )) then true
    else earlyErrors_rec r ctx.

  Section Extensions.
    Definition all_groups_in (r: RegexNode) : list RegexNode :=
      let (pattern, ctx) := r in
      List.filter ( fun r => match r with
        | (Group _ _, _) => true
        | _ => false
        end
        ) (Zipper.Walk.walk pattern ctx).

    (* Return the nth group INSIDE this node *)
    Definition nth_group_in {F} `{Result.AssertionError F} (r: RegexNode) (n: non_neg_integer): Result.Result RegexNode F :=
      let groups := all_groups_in r in
      groups[n].

    Definition nth_group {F} `{Result.AssertionError F} (r: Regex) (n: non_neg_integer): Result.Result RegexNode F :=
      nth_group_in (r, nil) n.

    Definition defines_groups_in {F} `{Result.AssertionError F} (r: RegexNode): bool :=
      List.length (all_groups_in r) >=? 1.

    Definition defines_groups {F} `{Result.AssertionError F} (r: Regex): bool :=
      defines_groups_in (r, nil).
  End Extensions.
End StaticSemantics.
