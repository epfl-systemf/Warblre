From Coq Require Import List Program.Equality PeanoNat.
From Warblre Require Import List Result Typeclasses Notation Numeric Characters Parameters.

(** >>
    22.2.1 Patterns

    The RegExp constructor applies the following grammar to the input pattern String. An error occurs if the
    grammar cannot interpret the String as an expansion of Pattern
<<*)
(* + 
    Note that our representation of Regexes differs from the the specification in some regards:
    - The grammar in the paper specification  has to care about parsing of regexes, and hence distinguishes between
      many different non-terminal (Pattern, Disjunction, Alternative, Term, Atom, Assertion, ...). We represent all
      of these non-terminals as one single [Regex] type.
      Additionally, this more relaxed representation allows to represent regexes which are prohibited by the standard
      grammar, but allowed under the grammar of annex B.1.2.
    - For the same reason, we do not include nodes such as "NonemptyClassRangesNoDash" (or any of the ".*NoDash"),
      which only exist to disambiguate the grammar.
    - Finally, and again for the same reason, nodes such as "DecimalDigits" are directly represented as numbers,
      rather than a sequence of digits which have to transformed into a number.
+*)

Module Patterns.
  Section Types.
    Local Definition String {T: Type} `{StringMarker T} := T.
    Local Definition Character {T: Type} `{CharacterMarker T} := T.
    Local Definition UnicodeProperty {T: Type} `{UnicodePropertyMarker T} := T.
    Context {Character_ String_ UnicodeProperty_: Type}
      `{CharacterMarker Character_} `{StringMarker String_} `{UnicodePropertyMarker UnicodeProperty_}.

    (*>> GroupName[UnicodeMode] :: <<*)
    (* + Groups name is abstract to string. +*)
    Definition GroupName `{StringMarker String} := String.

    (** >> CharacterClassEscape[UnicodeMode] :: <<*)
    Inductive CharacterClassEscape :=
      (*>> d <<*)
      | esc_d
      (*>> D <<*)
      | esc_D
      (*>> s <<*)
      | esc_s
      (*>> S <<*)
      | esc_S
      (*>> w <<*)
      | esc_w
      (*>> W <<*)
      | esc_W
      (*>> [+UnicodeMode] p{ UnicodePropertyValueExpression } <<*)
      | UnicodeProp (p: UnicodeProperty)
      (*>> [+UnicodeMode] P{ UnicodePropertyValueExpression } <<*)
      | UnicodePropNeg (p: UnicodeProperty).

    (** >> ControlEscape :: one of <<*)
    Inductive ControlEscape :=
    (*>> f <<*)
    | esc_f
    (*>> n <<*)
    | esc_n
    (*>> r <<*)
    | esc_r
    (*>> t <<*)
    | esc_t
    (*>> v <<*)
    | esc_v.

    (** >> RegExpUnicodeEscapeSequence[UnicodeMode] :: <<*)
    Inductive RegExpUnicodeEscapeSequence :=
    (*>> [+UnicodeMode] u HexLeadSurrogate \u HexTrailSurrogate  <<*)
    | Pair (lead tail: Hex4Digits)
    (*>> [+UnicodeMode] u HexLeadSurrogate  <<*)
    (*>> [+UnicodeMode] u HexTrailSurrogate <<*)
    (*>> [+UnicodeMode] u HexNonSurrogate <<*)
    (*>> [~UnicodeMode] u Hex4Digits <<*)
    | Lonely (digis: Hex4Digits)
    (*>> [+UnicodeMode] u{ CodePoint } <<*)
    | CodePoint (c: Character).

    (** >> CharacterEscape[UnicodeMode] :: <<*)
    Inductive CharacterEscape :=
    (*>> ControlEscape <<*)
    | ControlEsc (esc: ControlEscape)
    (*>> c AsciiLetter <<*)
    | AsciiControlEsc (l: AsciiLetter)
    (*>> 0 [lookahead ∉ DecimalDigit] <<*)
    | esc_Zero
    (*>> HexEscapeSequence <<*)
    | HexEscape (d1 d2: HexDigit)
    (*>> RegExpUnicodeEscapeSequence[?UnicodeMode]  <<*)
    | UnicodeEsc (seq: RegExpUnicodeEscapeSequence)
    (*>>  IdentityEscape[?UnicodeMode] <<*)
    | IdentityEsc (chr: Character).

    (** >> ClassEscape[UnicodeMode] :: <<*)
    Inductive ClassEscape :=
    (*>> b <<*)
    | esc_b
    (*>> [+UnicodeMode] - <<*)
    | esc_Dash
    (*>>  CharacterClassEscape[?UnicodeMode] <<*)
    | CCharacterClassEsc (esc: CharacterClassEscape)
    (*>>  CharacterEscape[?UnicodeMode] <<*)
    | CCharacterEsc (esc: CharacterEscape).

    (** >> AtomEscape[UnicodeMode, N] :: <<*)
    Inductive AtomEscape :=
    (*>> DecimalEscape <<*)
    | DecimalEsc (n: positive_integer)
    (*>> CharacterClassEscape[?UnicodeMode] <<*)
    | ACharacterClassEsc (esc: CharacterClassEscape)
    (*>> CharacterEscape[?UnicodeMode] <<*)
    | ACharacterEsc (esc: CharacterEscape)
    (*>> [+N] k GroupName[?UnicodeMode] <<*)
    | GroupEsc (id: GroupName).

    (** >> QuantifierPrefix :: <<*)
    Inductive QuantifierPrefix :=
    (*>> * <<*)
    | Star
    (*>> + <<*)
    | Plus
    (*>> ? <<*)
    | Question
    (*>> { DecimalDigits[~Sep] } <<*)
    | RepExact (count: non_neg_integer)
    (*>> { DecimalDigits[~Sep] ,} <<*)
    | RepPartialRange (min: non_neg_integer)
    (*>> { DecimalDigits[~Sep] , DecimalDigits[~Sep] } <<*)
    | RepRange (min: non_neg_integer) (max: non_neg_integer).

    (** >> Quantifier :: <<*)
    Inductive Quantifier :=
    (*>> QuantifierPrefix <<*)
    | Greedy (p: QuantifierPrefix)
    (*>> QuantifierPrefix ? <<*)
    | Lazy (p: QuantifierPrefix).

    (** >> ClassAtom :: <<*)
    (** >> ClassAtomNoDash :: <<*)
    Inductive ClassAtom :=
    (*>> - <<*)
    (*>> SourceCharacter but not one of \ or ] or - <<*)
    | SourceCharacter (chr: Character)
    (*>> \ ClassEscape[?UnicodeMode] <<*)
    | ClassEsc (esc: ClassEscape).

    (** >> ClassRanges :: <<*)
    (** >> NonemptyClassRanges :: <<*)
    (** >> NonemptyClassRangesNoDash :: <<*)
    Inductive ClassRanges :=
    (*>> [empty] <<*)
    | EmptyCR
    (*>> ClassAtom[?UnicodeMode] <<*)
    (*>> ClassAtom[?UnicodeMode] NonemptyClassRangesNoDash[?UnicodeMode] <<*)
    (*>> ClassAtomNoDash[?UnicodeMode] NonemptyClassRangesNoDash[?UnicodeMode] <<*)
    | ClassAtomCR (ca: ClassAtom) (t: ClassRanges)
    (*>> ClassAtom[?UnicodeMode] - ClassAtom[?UnicodeMode] ClassRanges[?UnicodeMode] <<*)
    (*>> ClassAtomNoDash[?UnicodeMode] - ClassAtom[?UnicodeMode] ClassRanges[?UnicodeMode] <<*)
    | RangeCR (l h: ClassAtom) (t: ClassRanges).

    (** >> CharacterClass[UnicodeMode] :: <<*)
    Inductive CharClass :=
    (*>> [ [lookahead ≠ ^] ClassRanges[?UnicodeMode] ] <<*)
    | NoninvertedCC (crs: ClassRanges)
    (*>> [^ ClassRanges[?UnicodeMode] ] <<*)
    | InvertedCC (crs: ClassRanges).

    (** >> Pattern :: <<*)
    (** >> Disjunction :: <<*)
    (** >> Alternative :: <<*)
    (** >> Term :: <<*)
    (** >> Assertion :: <<*)
    (** >> Atom :: <<*)
    Inductive Regex :=
    (*>> [empty] <<*)
    | Empty
    (*>> PatternCharacter <<*)
    | Char (chr: Character)
    (*>> . <<*)
    | Dot
    (*>> \ AtomEscape[?UnicodeMode, ?N] <<*)
    | AtomEsc (ae: AtomEscape)
    (*>> CharacterClass[?UnicodeMode] <<*)
    | CharacterClass (cc: CharClass)
    (*>> Alternative[?UnicodeMode, ?N] | Disjunction[?UnicodeMode, ?N] <<*)
    | Disjunction (r1 r2: Regex)
    (*>> Atom[?UnicodeMode, ?N] Quantifier <<*)
    | Quantified (r: Regex) (q: Quantifier)
    (*>> Alternative[?UnicodeMode, ?N] Term[?UnicodeMode, ?N] <<*)
    | Seq (r1 r2: Regex)
    (*>> ( GroupSpecifier[?UnicodeMode]opt Disjunction[?UnicodeMode, ?N] ) <<*)
    | Group (name: option GroupName) (r: Regex)
    (*>> ^ <<*)
    | InputStart
    (*>> $ <<*)
    | InputEnd
    (*>> \b <<*)
    | WordBoundary
    (*>> \B <<*)
    | NotWordBoundary
    (*>> (?= Disjunction[?UnicodeMode, ?N] ) <<*)
    | Lookahead (r: Regex)
    (*>> (?! Disjunction[?UnicodeMode, ?N] ) <<*)
    | NegativeLookahead (r: Regex)
    (*>> (?<= Disjunction[?UnicodeMode, ?N] ) <<*)
    | Lookbehind (r: Regex)
    (*>> (?<! Disjunction[?UnicodeMode, ?N] ) <<*)
    | NegativeLookbehind (r: Regex).
  End Types.

  Section EqDec.
    Context `{specParameters: Parameters}.

    #[export] #[refine] Instance eqdec_CharacterClassEscape: EqDec CharacterClassEscape := {}. 
    Proof. decide equality; apply EqDec.eq_dec. Defined.
    #[export] #[refine] Instance eqdec_ControlEscape: EqDec ControlEscape := {}.
    Proof. decide equality. Defined.
    #[export] #[refine] Instance eqdec_Hex4Digits: EqDec Hex4Digits := {}.
    Proof. decide equality; apply EqDec.eq_dec. Defined.
    #[export] #[refine] Instance eqdec_RegExpUnicodeEscapeSequence: EqDec RegExpUnicodeEscapeSequence := {}.
    Proof. decide equality; apply EqDec.eq_dec. Defined.
    #[export] #[refine] Instance eqdec_CharacterEscape: EqDec CharacterEscape := {}.
    Proof. decide equality; apply EqDec.eq_dec. Defined.
    #[export] #[refine] Instance eqdec_CClassEscape: EqDec ClassEscape := {}.
    Proof. decide equality; apply EqDec.eq_dec. Defined.
    #[export] #[refine] Instance eqdec_AtomEscape: EqDec AtomEscape := {}.
    Proof. decide equality; apply EqDec.eq_dec. Defined.
    #[export] #[refine] Instance eqdec_QuantifierPrefix: EqDec QuantifierPrefix := {}.
    Proof. decide equality; apply EqDec.eq_dec. Defined.
    #[export] #[refine] Instance eqdec_Quantifier: EqDec Quantifier := {}.
    Proof. decide equality; apply EqDec.eq_dec. Defined.
    #[export] #[refine] Instance eqdec_ClassAtom: EqDec ClassAtom := {}.
    Proof. decide equality; apply EqDec.eq_dec. Defined.
    #[export] #[refine] Instance eqdec_ClassRanges: EqDec ClassRanges := {}.
    Proof. decide equality; apply EqDec.eq_dec. Defined.
    #[export] #[refine] Instance eqdec_CharClass: EqDec CharClass := {}.
    Proof. decide equality; apply EqDec.eq_dec. Defined.
    #[export] #[refine] Instance eqdec_Regex: EqDec Regex := {}.
    Proof. decide equality; apply EqDec.eq_dec. Defined.
  End EqDec.
End Patterns.
