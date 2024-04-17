From Coq Require Import List Program.Equality PeanoNat.
From Warblre Require Import List Result Typeclasses Notation Numeric Characters.

(** 22.2.1 Patterns *)
(* The RegExp constructor applies the following grammar to the input pattern String. An error occurs if the
  grammar cannot interpret the String as an expansion of Pattern *)

Module Patterns. Section main.
  Context `{ep: CharacterInstance Σ}.

  (** GroupName :: *)
  Parameter GroupName: Type.
  Parameter GroupName_eq_dec: forall (l r: GroupName), {l=r} + {l<>r}.

  (** CharacterClassEscape :: *)
  Inductive CharacterClassEscape :=
    (* d *)
    | esc_d
    (* D *)
    | esc_D
    (* s *)
    | esc_s
    (* S *)
    | esc_S
    (* w *)
    | esc_w
    (* W *)
    | esc_W
    (* p *)
    | UnicodeProp (p: UnicodeProperty)
    (* P *)
    | UnicodePropNeg (p: UnicodeProperty).

  (** ControlEscape :: *)
  Inductive ControlEscape :=
  (* f *)
  | esc_f
  (* n *)
  | esc_n
  (* r *)
  | esc_r
  (* t *)
  | esc_t
  (* v *)
  | esc_v.

  (** RegExpUnicodeEscapeSequence :: *)
  Inductive RegExpUnicodeEscapeSequence :=
  | Pair (lead tail: Hex4Digits)
  | Lonely (digis: Hex4Digits)
  | CodePoint (c: Character).

  (** CharacterEscape :: *)
  Inductive CharacterEscape :=
  | ControlEsc (esc: ControlEscape)
  (* c *)
  | AsciiControlEsc (l: AsciiLetter)
  (* 0 *)
  | esc_Zero
  (* x *)
  | HexEscape (d1 d2: HexDigit)
  (* u *)
  | UnicodeEsc (seq: RegExpUnicodeEscapeSequence)
  | IdentityEsc (chr: Character).


  (** ClassEscape :: *)
  Inductive ClassEscape :=
  (* b *)
  | esc_b
  (* - *)
  | esc_Dash
  | CCharacterClassEsc (esc: CharacterClassEscape)
  | CCharacterEsc (esc: CharacterEscape).

  (** AtomEscape :: *)
  Inductive AtomEscape :=
  | DecimalEsc (n: positive_integer)
  | ACharacterClassEsc (esc: CharacterClassEscape)
  | ACharacterEsc (esc: CharacterEscape)
  | GroupEsc (id: GroupName).

  (** QuantifierPrefix :: *)
  Inductive QuantifierPrefix :=
  | Star
  | Plus
  | Question
  | RepExact (count: non_neg_integer)
  | RepPartialRange (min: non_neg_integer)
  | RepRange (min: non_neg_integer) (max: non_neg_integer).

  (** Quantifier :: *)
  Inductive Quantifier :=
  | Greedy (p: QuantifierPrefix)
  | Lazy (p: QuantifierPrefix).

  (** ClassAtom :: *)
  (** ClassAtomNoDash :: *)
  Inductive ClassAtom :=
  | SourceCharacter (chr: Character)
  | ClassEsc (esc: ClassEscape).

  (** ClassRanges :: *)
  (** NonemptyClassRanges :: *)
  (** NonemptyClassRangesNoDash :: *)
  Inductive ClassRanges :=
  | EmptyCR
  | ClassAtomCR (ca: ClassAtom) (t: ClassRanges)
  | RangeCR (l h: ClassAtom) (t: ClassRanges).

  (** CharacterClass :: *)
  Inductive CharClass :=
  | NoninvertedCC (crs: ClassRanges)
  | InvertedCC (crs: ClassRanges).

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

  Section EqDec.
    #[export] Instance eqdec_GroupName: EqDec GroupName := { eq_dec := GroupName_eq_dec; }.
    #[export] #[refine] Instance eqdec_CharacterClassEscape: EqDec CharacterClassEscape := {}. decide equality; solve [ apply EqDec.eq_dec | apply (@EqDec.eq_dec _ Character.unicode_property_eqdec) ]. Defined.
    #[export] #[refine] Instance eqdec_ControlEscape: EqDec ControlEscape := {}. decide equality. Defined.
    #[export] #[refine] Instance eqdec_Hex4Digits: EqDec Hex4Digits := {}.
      decide equality; try apply EqDec.eq_dec. Defined.
    #[export] #[refine] Instance eqdec_RegExpUnicodeEscapeSequence: EqDec RegExpUnicodeEscapeSequence := {}.
      decide equality; try apply EqDec.eq_dec. Defined.
    #[export] #[refine] Instance eqdec_CharacterEscape: EqDec CharacterEscape := {}.
      decide equality; try apply EqDec.eq_dec. Defined.
    #[export] #[refine] Instance eqdec_CClassEscape: EqDec ClassEscape := {}.
      decide equality; apply EqDec.eq_dec. Defined.
    #[export] #[refine] Instance eqdec_AtomEscape: EqDec AtomEscape := {}.
      decide equality; first [ apply EqDec.eq_dec ]. Defined.
    #[export] #[refine] Instance eqdec_QuantifierPrefix: EqDec QuantifierPrefix := {}.
      decide equality; apply EqDec.eq_dec. Defined.
    #[export] #[refine] Instance eqdec_Quantifier: EqDec Quantifier := {}.
      decide equality; apply EqDec.eq_dec. Defined.
    #[export] #[refine] Instance eqdec_ClassAtom: EqDec ClassAtom := {}.
      decide equality; apply EqDec.eq_dec. Defined.
    #[export] #[refine] Instance eqdec_ClassRanges: EqDec ClassRanges := {}.
      decide equality; apply EqDec.eq_dec. Defined.
    #[export] #[refine] Instance eqdec_CharClass: EqDec CharClass := {}.
      decide equality; apply EqDec.eq_dec. Defined.
    #[export] #[refine] Instance eqdec_Regex: EqDec Regex := {}.
      decide equality; apply EqDec.eq_dec. Defined.
  End EqDec.
End main. End Patterns.
