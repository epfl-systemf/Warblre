From Coq.Lists Require List.
From Coq.PArith Require Import BinPos.
From Coq.NArith Require Import BinNat.
From MenhirLib Require Main.
From MenhirLib Require Version.
Import List.ListNotations.

Definition version_check : unit := MenhirLib.Version.require_20230608.

Unset Elimination Schemes.

Inductive token : Type :=
| ZERO : unit%type -> token
| UPW : unit%type -> token
| UPS : unit%type -> token
| UPP : unit%type -> token
| UPD : unit%type -> token
| UPB : unit%type -> token
| STAR : unit%type -> token
| RPAR : unit%type -> token
| RBRACK : unit%type -> token
| RBRAC : unit%type -> token
| QMARK : unit%type -> token
| PLUS : unit%type -> token
| NZDIGIT :        (char)%type -> token
| MORE : unit%type -> token
| MINUS : unit%type -> token
| LPAR : unit%type -> token
| LOWX : unit%type -> token
| LOWW : unit%type -> token
| LOWV : unit%type -> token
| LOWU : unit%type -> token
| LOWT : unit%type -> token
| LOWS : unit%type -> token
| LOWR : unit%type -> token
| LOWP : unit%type -> token
| LOWN : unit%type -> token
| LOWK : unit%type -> token
| LOWF : unit%type -> token
| LOWD : unit%type -> token
| LOWB : unit%type -> token
| LESS : unit%type -> token
| LBRACK : unit%type -> token
| LBRAC : unit%type -> token
| HAT : unit%type -> token
| EXCL : unit%type -> token
| EQUAL : unit%type -> token
| EOF : unit%type -> token
| DOT : unit%type -> token
| DOLLAR : unit%type -> token
| COMMA : unit%type -> token
| COLONS : unit%type -> token
| CHAR :        (char)%type -> token
| BACKSL : unit%type -> token
| ALT : unit%type -> token.

Module Import Gram <: MenhirLib.Grammar.T.

Local Obligation Tactic := let x := fresh in intro x; case x; reflexivity.

Inductive terminal' : Set :=
| ALT't
| BACKSL't
| CHAR't
| COLONS't
| COMMA't
| DOLLAR't
| DOT't
| EOF't
| EQUAL't
| EXCL't
| HAT't
| LBRAC't
| LBRACK't
| LESS't
| LOWB't
| LOWD't
| LOWF't
| LOWK't
| LOWN't
| LOWP't
| LOWR't
| LOWS't
| LOWT't
| LOWU't
| LOWV't
| LOWW't
| LOWX't
| LPAR't
| MINUS't
| MORE't
| NZDIGIT't
| PLUS't
| QMARK't
| RBRAC't
| RBRACK't
| RPAR't
| STAR't
| UPB't
| UPD't
| UPP't
| UPS't
| UPW't
| ZERO't.
Definition terminal := terminal'.

Global Program Instance terminalNum : MenhirLib.Alphabet.Numbered terminal :=
  { inj := fun x => match x return _ with
    | ALT't => 1%positive
    | BACKSL't => 2%positive
    | CHAR't => 3%positive
    | COLONS't => 4%positive
    | COMMA't => 5%positive
    | DOLLAR't => 6%positive
    | DOT't => 7%positive
    | EOF't => 8%positive
    | EQUAL't => 9%positive
    | EXCL't => 10%positive
    | HAT't => 11%positive
    | LBRAC't => 12%positive
    | LBRACK't => 13%positive
    | LESS't => 14%positive
    | LOWB't => 15%positive
    | LOWD't => 16%positive
    | LOWF't => 17%positive
    | LOWK't => 18%positive
    | LOWN't => 19%positive
    | LOWP't => 20%positive
    | LOWR't => 21%positive
    | LOWS't => 22%positive
    | LOWT't => 23%positive
    | LOWU't => 24%positive
    | LOWV't => 25%positive
    | LOWW't => 26%positive
    | LOWX't => 27%positive
    | LPAR't => 28%positive
    | MINUS't => 29%positive
    | MORE't => 30%positive
    | NZDIGIT't => 31%positive
    | PLUS't => 32%positive
    | QMARK't => 33%positive
    | RBRAC't => 34%positive
    | RBRACK't => 35%positive
    | RPAR't => 36%positive
    | STAR't => 37%positive
    | UPB't => 38%positive
    | UPD't => 39%positive
    | UPP't => 40%positive
    | UPS't => 41%positive
    | UPW't => 42%positive
    | ZERO't => 43%positive
    end;
    surj := (fun n => match n return _ with
    | 1%positive => ALT't
    | 2%positive => BACKSL't
    | 3%positive => CHAR't
    | 4%positive => COLONS't
    | 5%positive => COMMA't
    | 6%positive => DOLLAR't
    | 7%positive => DOT't
    | 8%positive => EOF't
    | 9%positive => EQUAL't
    | 10%positive => EXCL't
    | 11%positive => HAT't
    | 12%positive => LBRAC't
    | 13%positive => LBRACK't
    | 14%positive => LESS't
    | 15%positive => LOWB't
    | 16%positive => LOWD't
    | 17%positive => LOWF't
    | 18%positive => LOWK't
    | 19%positive => LOWN't
    | 20%positive => LOWP't
    | 21%positive => LOWR't
    | 22%positive => LOWS't
    | 23%positive => LOWT't
    | 24%positive => LOWU't
    | 25%positive => LOWV't
    | 26%positive => LOWW't
    | 27%positive => LOWX't
    | 28%positive => LPAR't
    | 29%positive => MINUS't
    | 30%positive => MORE't
    | 31%positive => NZDIGIT't
    | 32%positive => PLUS't
    | 33%positive => QMARK't
    | 34%positive => RBRAC't
    | 35%positive => RBRACK't
    | 36%positive => RPAR't
    | 37%positive => STAR't
    | 38%positive => UPB't
    | 39%positive => UPD't
    | 40%positive => UPP't
    | 41%positive => UPS't
    | 42%positive => UPW't
    | 43%positive => ZERO't
    | _ => ALT't
    end)%Z;
    inj_bound := 43%positive }.
Global Instance TerminalAlph : MenhirLib.Alphabet.Alphabet terminal := _.

Inductive nonterminal' : Set :=
| alternative'nt
| assertion'nt
| atom'nt
| decimaldigit'nt
| decimaldigits'nt
| decimaldigits_'nt
| disjunction'nt
| main'nt
| pattern'nt
| patterncharacter'nt
| quantifier'nt
| term'nt.
Definition nonterminal := nonterminal'.

Global Program Instance nonterminalNum : MenhirLib.Alphabet.Numbered nonterminal :=
  { inj := fun x => match x return _ with
    | alternative'nt => 1%positive
    | assertion'nt => 2%positive
    | atom'nt => 3%positive
    | decimaldigit'nt => 4%positive
    | decimaldigits'nt => 5%positive
    | decimaldigits_'nt => 6%positive
    | disjunction'nt => 7%positive
    | main'nt => 8%positive
    | pattern'nt => 9%positive
    | patterncharacter'nt => 10%positive
    | quantifier'nt => 11%positive
    | term'nt => 12%positive
    end;
    surj := (fun n => match n return _ with
    | 1%positive => alternative'nt
    | 2%positive => assertion'nt
    | 3%positive => atom'nt
    | 4%positive => decimaldigit'nt
    | 5%positive => decimaldigits'nt
    | 6%positive => decimaldigits_'nt
    | 7%positive => disjunction'nt
    | 8%positive => main'nt
    | 9%positive => pattern'nt
    | 10%positive => patterncharacter'nt
    | 11%positive => quantifier'nt
    | 12%positive => term'nt
    | _ => alternative'nt
    end)%Z;
    inj_bound := 12%positive }.
Global Instance NonTerminalAlph : MenhirLib.Alphabet.Alphabet nonterminal := _.

Include MenhirLib.Grammar.Symbol.

Definition terminal_semantic_type (t:terminal) : Type:=
  match t with
  | ZERO't => unit%type
  | UPW't => unit%type
  | UPS't => unit%type
  | UPP't => unit%type
  | UPD't => unit%type
  | UPB't => unit%type
  | STAR't => unit%type
  | RPAR't => unit%type
  | RBRACK't => unit%type
  | RBRAC't => unit%type
  | QMARK't => unit%type
  | PLUS't => unit%type
  | NZDIGIT't =>        (char)%type
  | MORE't => unit%type
  | MINUS't => unit%type
  | LPAR't => unit%type
  | LOWX't => unit%type
  | LOWW't => unit%type
  | LOWV't => unit%type
  | LOWU't => unit%type
  | LOWT't => unit%type
  | LOWS't => unit%type
  | LOWR't => unit%type
  | LOWP't => unit%type
  | LOWN't => unit%type
  | LOWK't => unit%type
  | LOWF't => unit%type
  | LOWD't => unit%type
  | LOWB't => unit%type
  | LESS't => unit%type
  | LBRACK't => unit%type
  | LBRAC't => unit%type
  | HAT't => unit%type
  | EXCL't => unit%type
  | EQUAL't => unit%type
  | EOF't => unit%type
  | DOT't => unit%type
  | DOLLAR't => unit%type
  | COMMA't => unit%type
  | COLONS't => unit%type
  | CHAR't =>        (char)%type
  | BACKSL't => unit%type
  | ALT't => unit%type
  end.

Definition nonterminal_semantic_type (nt:nonterminal) : Type:=
  match nt with
  | term'nt =>        (Warblre.Extracted.Patterns.coq_Regex)%type
  | quantifier'nt =>        (Warblre.Extracted.Patterns.coq_Quantifier)%type
  | patterncharacter'nt =>        (char)%type
  | pattern'nt =>        (Warblre.Extracted.Patterns.coq_Regex)%type
  | main'nt =>        (Warblre.Extracted.Patterns.coq_Regex)%type
  | disjunction'nt =>        (Warblre.Extracted.Patterns.coq_Regex)%type
  | decimaldigits_'nt =>        (string)%type
  | decimaldigits'nt =>        (int)%type
  | decimaldigit'nt =>        (char)%type
  | atom'nt =>        (Warblre.Extracted.Patterns.coq_Regex)%type
  | assertion'nt =>        (Warblre.Extracted.Patterns.coq_Regex)%type
  | alternative'nt =>        (Warblre.Extracted.Patterns.coq_Regex)%type
  end.

Definition symbol_semantic_type (s:symbol) : Type:=
  match s with
  | T t => terminal_semantic_type t
  | NT nt => nonterminal_semantic_type nt
  end.

Definition token := token.

Definition token_term (tok : token) : terminal :=
  match tok with
  | ZERO _ => ZERO't
  | UPW _ => UPW't
  | UPS _ => UPS't
  | UPP _ => UPP't
  | UPD _ => UPD't
  | UPB _ => UPB't
  | STAR _ => STAR't
  | RPAR _ => RPAR't
  | RBRACK _ => RBRACK't
  | RBRAC _ => RBRAC't
  | QMARK _ => QMARK't
  | PLUS _ => PLUS't
  | NZDIGIT _ => NZDIGIT't
  | MORE _ => MORE't
  | MINUS _ => MINUS't
  | LPAR _ => LPAR't
  | LOWX _ => LOWX't
  | LOWW _ => LOWW't
  | LOWV _ => LOWV't
  | LOWU _ => LOWU't
  | LOWT _ => LOWT't
  | LOWS _ => LOWS't
  | LOWR _ => LOWR't
  | LOWP _ => LOWP't
  | LOWN _ => LOWN't
  | LOWK _ => LOWK't
  | LOWF _ => LOWF't
  | LOWD _ => LOWD't
  | LOWB _ => LOWB't
  | LESS _ => LESS't
  | LBRACK _ => LBRACK't
  | LBRAC _ => LBRAC't
  | HAT _ => HAT't
  | EXCL _ => EXCL't
  | EQUAL _ => EQUAL't
  | EOF _ => EOF't
  | DOT _ => DOT't
  | DOLLAR _ => DOLLAR't
  | COMMA _ => COMMA't
  | COLONS _ => COLONS't
  | CHAR _ => CHAR't
  | BACKSL _ => BACKSL't
  | ALT _ => ALT't
  end.

Definition token_sem (tok : token) : symbol_semantic_type (T (token_term tok)) :=
  match tok with
  | ZERO x => x
  | UPW x => x
  | UPS x => x
  | UPP x => x
  | UPD x => x
  | UPB x => x
  | STAR x => x
  | RPAR x => x
  | RBRACK x => x
  | RBRAC x => x
  | QMARK x => x
  | PLUS x => x
  | NZDIGIT x => x
  | MORE x => x
  | MINUS x => x
  | LPAR x => x
  | LOWX x => x
  | LOWW x => x
  | LOWV x => x
  | LOWU x => x
  | LOWT x => x
  | LOWS x => x
  | LOWR x => x
  | LOWP x => x
  | LOWN x => x
  | LOWK x => x
  | LOWF x => x
  | LOWD x => x
  | LOWB x => x
  | LESS x => x
  | LBRACK x => x
  | LBRAC x => x
  | HAT x => x
  | EXCL x => x
  | EQUAL x => x
  | EOF x => x
  | DOT x => x
  | DOLLAR x => x
  | COMMA x => x
  | COLONS x => x
  | CHAR x => x
  | BACKSL x => x
  | ALT x => x
  end.

Inductive production' : Set :=
| Prod'term'2
| Prod'term'1
| Prod'term'0
| Prod'quantifier'11
| Prod'quantifier'10
| Prod'quantifier'9
| Prod'quantifier'8
| Prod'quantifier'7
| Prod'quantifier'6
| Prod'quantifier'5
| Prod'quantifier'4
| Prod'quantifier'3
| Prod'quantifier'2
| Prod'quantifier'1
| Prod'quantifier'0
| Prod'patterncharacter'30
| Prod'patterncharacter'29
| Prod'patterncharacter'28
| Prod'patterncharacter'27
| Prod'patterncharacter'26
| Prod'patterncharacter'25
| Prod'patterncharacter'24
| Prod'patterncharacter'23
| Prod'patterncharacter'22
| Prod'patterncharacter'21
| Prod'patterncharacter'20
| Prod'patterncharacter'19
| Prod'patterncharacter'18
| Prod'patterncharacter'17
| Prod'patterncharacter'16
| Prod'patterncharacter'15
| Prod'patterncharacter'14
| Prod'patterncharacter'13
| Prod'patterncharacter'12
| Prod'patterncharacter'11
| Prod'patterncharacter'10
| Prod'patterncharacter'9
| Prod'patterncharacter'8
| Prod'patterncharacter'7
| Prod'patterncharacter'6
| Prod'patterncharacter'5
| Prod'patterncharacter'4
| Prod'patterncharacter'3
| Prod'patterncharacter'2
| Prod'patterncharacter'1
| Prod'patterncharacter'0
| Prod'pattern'0
| Prod'main'0
| Prod'disjunction'1
| Prod'disjunction'0
| Prod'decimaldigits_'1
| Prod'decimaldigits_'0
| Prod'decimaldigits'0
| Prod'decimaldigit'1
| Prod'decimaldigit'0
| Prod'atom'1
| Prod'atom'0
| Prod'assertion'3
| Prod'assertion'2
| Prod'assertion'1
| Prod'assertion'0
| Prod'alternative'2
| Prod'alternative'1
| Prod'alternative'0.
Definition production := production'.

Global Program Instance productionNum : MenhirLib.Alphabet.Numbered production :=
  { inj := fun x => match x return _ with
    | Prod'term'2 => 1%positive
    | Prod'term'1 => 2%positive
    | Prod'term'0 => 3%positive
    | Prod'quantifier'11 => 4%positive
    | Prod'quantifier'10 => 5%positive
    | Prod'quantifier'9 => 6%positive
    | Prod'quantifier'8 => 7%positive
    | Prod'quantifier'7 => 8%positive
    | Prod'quantifier'6 => 9%positive
    | Prod'quantifier'5 => 10%positive
    | Prod'quantifier'4 => 11%positive
    | Prod'quantifier'3 => 12%positive
    | Prod'quantifier'2 => 13%positive
    | Prod'quantifier'1 => 14%positive
    | Prod'quantifier'0 => 15%positive
    | Prod'patterncharacter'30 => 16%positive
    | Prod'patterncharacter'29 => 17%positive
    | Prod'patterncharacter'28 => 18%positive
    | Prod'patterncharacter'27 => 19%positive
    | Prod'patterncharacter'26 => 20%positive
    | Prod'patterncharacter'25 => 21%positive
    | Prod'patterncharacter'24 => 22%positive
    | Prod'patterncharacter'23 => 23%positive
    | Prod'patterncharacter'22 => 24%positive
    | Prod'patterncharacter'21 => 25%positive
    | Prod'patterncharacter'20 => 26%positive
    | Prod'patterncharacter'19 => 27%positive
    | Prod'patterncharacter'18 => 28%positive
    | Prod'patterncharacter'17 => 29%positive
    | Prod'patterncharacter'16 => 30%positive
    | Prod'patterncharacter'15 => 31%positive
    | Prod'patterncharacter'14 => 32%positive
    | Prod'patterncharacter'13 => 33%positive
    | Prod'patterncharacter'12 => 34%positive
    | Prod'patterncharacter'11 => 35%positive
    | Prod'patterncharacter'10 => 36%positive
    | Prod'patterncharacter'9 => 37%positive
    | Prod'patterncharacter'8 => 38%positive
    | Prod'patterncharacter'7 => 39%positive
    | Prod'patterncharacter'6 => 40%positive
    | Prod'patterncharacter'5 => 41%positive
    | Prod'patterncharacter'4 => 42%positive
    | Prod'patterncharacter'3 => 43%positive
    | Prod'patterncharacter'2 => 44%positive
    | Prod'patterncharacter'1 => 45%positive
    | Prod'patterncharacter'0 => 46%positive
    | Prod'pattern'0 => 47%positive
    | Prod'main'0 => 48%positive
    | Prod'disjunction'1 => 49%positive
    | Prod'disjunction'0 => 50%positive
    | Prod'decimaldigits_'1 => 51%positive
    | Prod'decimaldigits_'0 => 52%positive
    | Prod'decimaldigits'0 => 53%positive
    | Prod'decimaldigit'1 => 54%positive
    | Prod'decimaldigit'0 => 55%positive
    | Prod'atom'1 => 56%positive
    | Prod'atom'0 => 57%positive
    | Prod'assertion'3 => 58%positive
    | Prod'assertion'2 => 59%positive
    | Prod'assertion'1 => 60%positive
    | Prod'assertion'0 => 61%positive
    | Prod'alternative'2 => 62%positive
    | Prod'alternative'1 => 63%positive
    | Prod'alternative'0 => 64%positive
    end;
    surj := (fun n => match n return _ with
    | 1%positive => Prod'term'2
    | 2%positive => Prod'term'1
    | 3%positive => Prod'term'0
    | 4%positive => Prod'quantifier'11
    | 5%positive => Prod'quantifier'10
    | 6%positive => Prod'quantifier'9
    | 7%positive => Prod'quantifier'8
    | 8%positive => Prod'quantifier'7
    | 9%positive => Prod'quantifier'6
    | 10%positive => Prod'quantifier'5
    | 11%positive => Prod'quantifier'4
    | 12%positive => Prod'quantifier'3
    | 13%positive => Prod'quantifier'2
    | 14%positive => Prod'quantifier'1
    | 15%positive => Prod'quantifier'0
    | 16%positive => Prod'patterncharacter'30
    | 17%positive => Prod'patterncharacter'29
    | 18%positive => Prod'patterncharacter'28
    | 19%positive => Prod'patterncharacter'27
    | 20%positive => Prod'patterncharacter'26
    | 21%positive => Prod'patterncharacter'25
    | 22%positive => Prod'patterncharacter'24
    | 23%positive => Prod'patterncharacter'23
    | 24%positive => Prod'patterncharacter'22
    | 25%positive => Prod'patterncharacter'21
    | 26%positive => Prod'patterncharacter'20
    | 27%positive => Prod'patterncharacter'19
    | 28%positive => Prod'patterncharacter'18
    | 29%positive => Prod'patterncharacter'17
    | 30%positive => Prod'patterncharacter'16
    | 31%positive => Prod'patterncharacter'15
    | 32%positive => Prod'patterncharacter'14
    | 33%positive => Prod'patterncharacter'13
    | 34%positive => Prod'patterncharacter'12
    | 35%positive => Prod'patterncharacter'11
    | 36%positive => Prod'patterncharacter'10
    | 37%positive => Prod'patterncharacter'9
    | 38%positive => Prod'patterncharacter'8
    | 39%positive => Prod'patterncharacter'7
    | 40%positive => Prod'patterncharacter'6
    | 41%positive => Prod'patterncharacter'5
    | 42%positive => Prod'patterncharacter'4
    | 43%positive => Prod'patterncharacter'3
    | 44%positive => Prod'patterncharacter'2
    | 45%positive => Prod'patterncharacter'1
    | 46%positive => Prod'patterncharacter'0
    | 47%positive => Prod'pattern'0
    | 48%positive => Prod'main'0
    | 49%positive => Prod'disjunction'1
    | 50%positive => Prod'disjunction'0
    | 51%positive => Prod'decimaldigits_'1
    | 52%positive => Prod'decimaldigits_'0
    | 53%positive => Prod'decimaldigits'0
    | 54%positive => Prod'decimaldigit'1
    | 55%positive => Prod'decimaldigit'0
    | 56%positive => Prod'atom'1
    | 57%positive => Prod'atom'0
    | 58%positive => Prod'assertion'3
    | 59%positive => Prod'assertion'2
    | 60%positive => Prod'assertion'1
    | 61%positive => Prod'assertion'0
    | 62%positive => Prod'alternative'2
    | 63%positive => Prod'alternative'1
    | 64%positive => Prod'alternative'0
    | _ => Prod'term'2
    end)%Z;
    inj_bound := 64%positive }.
Global Instance ProductionAlph : MenhirLib.Alphabet.Alphabet production := _.

Definition prod_contents (p:production) :
  { p:nonterminal * list symbol &
    MenhirLib.Grammar.arrows_right
      (symbol_semantic_type (NT (fst p)))
      (List.map symbol_semantic_type (snd p)) }
 :=
  let box := existT (fun p =>
    MenhirLib.Grammar.arrows_right
      (symbol_semantic_type (NT (fst p)))
      (List.map symbol_semantic_type (snd p)) )
  in
  match p with
  | Prod'alternative'0 => box
    (alternative'nt, [NT term'nt; NT alternative'nt]%list)
    (fun t a =>
                         ( Warblre.Extracted.Patterns.Seq(a,t) )
)
  | Prod'alternative'1 => box
    (alternative'nt, [NT term'nt]%list)
    (fun t =>
           ( t )
)
  | Prod'alternative'2 => box
    (alternative'nt, []%list)
    (
    ( Warblre.Extracted.Patterns.Empty )
)
  | Prod'assertion'0 => box
    (assertion'nt, [T RPAR't; NT disjunction'nt; T EQUAL't; T QMARK't; T LPAR't]%list)
    (fun _5 d _3 _2 _1 =>
                                        ( Warblre.Extracted.Patterns.Lookahead(d) )
)
  | Prod'assertion'1 => box
    (assertion'nt, [T RPAR't; NT disjunction'nt; T EXCL't; T QMARK't; T LPAR't]%list)
    (fun _5 d _3 _2 _1 =>
                                       ( Warblre.Extracted.Patterns.NegativeLookahead(d) )
)
  | Prod'assertion'2 => box
    (assertion'nt, [T RPAR't; NT disjunction'nt; T EQUAL't; T LESS't; T QMARK't; T LPAR't]%list)
    (fun _6 d _4 _3 _2 _1 =>
                                             ( Warblre.Extracted.Patterns.Lookbehind(d) )
)
  | Prod'assertion'3 => box
    (assertion'nt, [T RPAR't; NT disjunction'nt; T EXCL't; T LESS't; T QMARK't; T LPAR't]%list)
    (fun _6 d _4 _3 _2 _1 =>
                                            ( Warblre.Extracted.Patterns.NegativeLookbehind(d) )
)
  | Prod'atom'0 => box
    (atom'nt, [NT patterncharacter'nt]%list)
    (fun c =>
                       ( Warblre.Extracted.Patterns.Char(c) )
)
  | Prod'atom'1 => box
    (atom'nt, [T DOT't]%list)
    (fun _1 =>
        ( Warblre.Extracted.Patterns.Dot )
)
  | Prod'decimaldigit'0 => box
    (decimaldigit'nt, [T NZDIGIT't]%list)
    (fun nz =>
               ( nz )
)
  | Prod'decimaldigit'1 => box
    (decimaldigit'nt, [T ZERO't]%list)
    (fun _1 =>
         ( '0' )
)
  | Prod'decimaldigits'0 => box
    (decimaldigits'nt, [NT decimaldigits_'nt]%list)
    (fun d =>
                     ( int_of_string d )
)
  | Prod'decimaldigits_'0 => box
    (decimaldigits_'nt, [NT decimaldigit'nt; NT decimaldigits_'nt]%list)
    (fun d2 d1 =>
                                      ( d1 ^ String.make 1 d2 )
)
  | Prod'decimaldigits_'1 => box
    (decimaldigits_'nt, [NT decimaldigit'nt]%list)
    (fun d =>
                   ( String.make 1 d )
)
  | Prod'disjunction'0 => box
    (disjunction'nt, [NT alternative'nt]%list)
    (fun a =>
                  ( a )
)
  | Prod'disjunction'1 => box
    (disjunction'nt, [NT disjunction'nt; T ALT't; NT alternative'nt]%list)
    (fun d _2 a =>
                                    ( Warblre.Extracted.Patterns.Disjunction(a,d) )
)
  | Prod'main'0 => box
    (main'nt, [T EOF't; NT pattern'nt]%list)
    (fun _2 r =>
                    ( r )
)
  | Prod'pattern'0 => box
    (pattern'nt, [NT disjunction'nt]%list)
    (fun d =>
                  ( d )
)
  | Prod'patterncharacter'0 => box
    (patterncharacter'nt, [T CHAR't]%list)
    (fun c =>
           ( c )
)
  | Prod'patterncharacter'1 => box
    (patterncharacter'nt, [T LOWB't]%list)
    (fun _1 =>
         ( 'b' )
)
  | Prod'patterncharacter'2 => box
    (patterncharacter'nt, [T UPB't]%list)
    (fun _1 =>
        ( 'B' )
)
  | Prod'patterncharacter'3 => box
    (patterncharacter'nt, [T LOWD't]%list)
    (fun _1 =>
         ( 'd' )
)
  | Prod'patterncharacter'4 => box
    (patterncharacter'nt, [T UPD't]%list)
    (fun _1 =>
        ( 'D' )
)
  | Prod'patterncharacter'5 => box
    (patterncharacter'nt, [T LOWS't]%list)
    (fun _1 =>
         ( 's' )
)
  | Prod'patterncharacter'6 => box
    (patterncharacter'nt, [T UPS't]%list)
    (fun _1 =>
        ( 'S' )
)
  | Prod'patterncharacter'7 => box
    (patterncharacter'nt, [T LOWW't]%list)
    (fun _1 =>
         ( 'w' )
)
  | Prod'patterncharacter'8 => box
    (patterncharacter'nt, [T UPW't]%list)
    (fun _1 =>
        ( 'W' )
)
  | Prod'patterncharacter'9 => box
    (patterncharacter'nt, [T LOWF't]%list)
    (fun _1 =>
         ( 'f' )
)
  | Prod'patterncharacter'10 => box
    (patterncharacter'nt, [T LOWN't]%list)
    (fun _1 =>
         ( 'n' )
)
  | Prod'patterncharacter'11 => box
    (patterncharacter'nt, [T LOWR't]%list)
    (fun _1 =>
         ( 'r' )
)
  | Prod'patterncharacter'12 => box
    (patterncharacter'nt, [T LOWT't]%list)
    (fun _1 =>
         ( 't' )
)
  | Prod'patterncharacter'13 => box
    (patterncharacter'nt, [T LOWV't]%list)
    (fun _1 =>
         ( 'v' )
)
  | Prod'patterncharacter'14 => box
    (patterncharacter'nt, [T LOWK't]%list)
    (fun _1 =>
         ( 'k' )
)
  | Prod'patterncharacter'15 => box
    (patterncharacter'nt, [T LOWX't]%list)
    (fun _1 =>
         ( 'x' )
)
  | Prod'patterncharacter'16 => box
    (patterncharacter'nt, [T LOWU't]%list)
    (fun _1 =>
         ( 'u' )
)
  | Prod'patterncharacter'17 => box
    (patterncharacter'nt, [T LOWP't]%list)
    (fun _1 =>
         ( 'p' )
)
  | Prod'patterncharacter'18 => box
    (patterncharacter'nt, [T UPP't]%list)
    (fun _1 =>
        ( 'P' )
)
  | Prod'patterncharacter'19 => box
    (patterncharacter'nt, [T COMMA't]%list)
    (fun _1 =>
          ( ',' )
)
  | Prod'patterncharacter'20 => box
    (patterncharacter'nt, [T COLONS't]%list)
    (fun _1 =>
           ( ':' )
)
  | Prod'patterncharacter'21 => box
    (patterncharacter'nt, [T LESS't]%list)
    (fun _1 =>
         ( '<' )
)
  | Prod'patterncharacter'22 => box
    (patterncharacter'nt, [T MORE't]%list)
    (fun _1 =>
         ( '>' )
)
  | Prod'patterncharacter'23 => box
    (patterncharacter'nt, [T EQUAL't]%list)
    (fun _1 =>
          ( '=' )
)
  | Prod'patterncharacter'24 => box
    (patterncharacter'nt, [T MINUS't]%list)
    (fun _1 =>
          ( '-' )
)
  | Prod'patterncharacter'25 => box
    (patterncharacter'nt, [T EXCL't]%list)
    (fun _1 =>
         ( '!' )
)
  | Prod'patterncharacter'26 => box
    (patterncharacter'nt, [T LBRAC't]%list)
    (fun _1 =>
          ( '{' )
)
  | Prod'patterncharacter'27 => box
    (patterncharacter'nt, [T RBRAC't]%list)
    (fun _1 =>
          ( '}' )
)
  | Prod'patterncharacter'28 => box
    (patterncharacter'nt, [T LBRACK't]%list)
    (fun _1 =>
           ( '[' )
)
  | Prod'patterncharacter'29 => box
    (patterncharacter'nt, [T RBRACK't]%list)
    (fun _1 =>
           ( ']' )
)
  | Prod'patterncharacter'30 => box
    (patterncharacter'nt, [NT decimaldigit'nt]%list)
    (fun d =>
                   ( d )
)
  | Prod'quantifier'0 => box
    (quantifier'nt, [T STAR't]%list)
    (fun _1 =>
         ( Warblre.Extracted.Patterns.Greedy(Warblre.Extracted.Patterns.Star) )
)
  | Prod'quantifier'1 => box
    (quantifier'nt, [T QMARK't; T STAR't]%list)
    (fun _2 _1 =>
               ( Warblre.Extracted.Patterns.Lazy(Warblre.Extracted.Patterns.Star) )
)
  | Prod'quantifier'2 => box
    (quantifier'nt, [T PLUS't]%list)
    (fun _1 =>
         ( Warblre.Extracted.Patterns.Greedy(Warblre.Extracted.Patterns.Plus) )
)
  | Prod'quantifier'3 => box
    (quantifier'nt, [T QMARK't; T PLUS't]%list)
    (fun _2 _1 =>
               ( Warblre.Extracted.Patterns.Lazy(Warblre.Extracted.Patterns.Plus) )
)
  | Prod'quantifier'4 => box
    (quantifier'nt, [T QMARK't]%list)
    (fun _1 =>
          ( Warblre.Extracted.Patterns.Greedy(Warblre.Extracted.Patterns.Question) )
)
  | Prod'quantifier'5 => box
    (quantifier'nt, [T QMARK't; T QMARK't]%list)
    (fun _2 _1 =>
                ( Warblre.Extracted.Patterns.Lazy(Warblre.Extracted.Patterns.Question) )
)
  | Prod'quantifier'6 => box
    (quantifier'nt, [T RBRAC't; NT decimaldigits'nt; T LBRAC't]%list)
    (fun _3 d _1 =>
                                ( Warblre.Extracted.Patterns.Greedy(Warblre.Extracted.Patterns.RepExact(d)) )
)
  | Prod'quantifier'7 => box
    (quantifier'nt, [T QMARK't; T RBRAC't; NT decimaldigits'nt; T LBRAC't]%list)
    (fun _4 _3 d _1 =>
                                     ( Warblre.Extracted.Patterns.Lazy(Warblre.Extracted.Patterns.RepExact(d)) )
)
  | Prod'quantifier'8 => box
    (quantifier'nt, [T RBRAC't; T COMMA't; NT decimaldigits'nt; T LBRAC't]%list)
    (fun _4 _3 d _1 =>
                                      ( Warblre.Extracted.Patterns.Greedy(Warblre.Extracted.Patterns.RepPartialRange(d)) )
)
  | Prod'quantifier'9 => box
    (quantifier'nt, [T QMARK't; T RBRAC't; T COMMA't; NT decimaldigits'nt; T LBRAC't]%list)
    (fun _5 _4 _3 d _1 =>
                                            ( Warblre.Extracted.Patterns.Lazy(Warblre.Extracted.Patterns.RepPartialRange(d)) )
)
  | Prod'quantifier'10 => box
    (quantifier'nt, [T RBRAC't; NT decimaldigits'nt; T COMMA't; NT decimaldigits'nt; T LBRAC't]%list)
    (fun _5 dmax _3 dmin _1 =>
                                                            ( Warblre.Extracted.Patterns.Greedy(Warblre.Extracted.Patterns.RepRange(dmin,dmax)) )
)
  | Prod'quantifier'11 => box
    (quantifier'nt, [T QMARK't; T RBRAC't; NT decimaldigits'nt; T COMMA't; NT decimaldigits'nt; T LBRAC't]%list)
    (fun _6 _5 dmax _3 dmin _1 =>
                                                                  ( Warblre.Extracted.Patterns.Lazy(Warblre.Extracted.Patterns.RepRange(dmin,dmax)) )
)
  | Prod'term'0 => box
    (term'nt, [NT assertion'nt]%list)
    (fun a =>
                ( a )
)
  | Prod'term'1 => box
    (term'nt, [NT atom'nt]%list)
    (fun a =>
           ( a )
)
  | Prod'term'2 => box
    (term'nt, [NT quantifier'nt; NT atom'nt]%list)
    (fun q a =>
                        ( Warblre.Extracted.Patterns.Quantified(a,q) )
)
  end.

Definition prod_lhs (p:production) :=
  fst (projT1 (prod_contents p)).
Definition prod_rhs_rev (p:production) :=
  snd (projT1 (prod_contents p)).
Definition prod_action (p:production) :=
  projT2 (prod_contents p).

Include MenhirLib.Grammar.Defs.

End Gram.

Module Aut <: MenhirLib.Automaton.T.

Local Obligation Tactic := let x := fresh in intro x; case x; reflexivity.

Module Gram := Gram.
Module GramDefs := Gram.

Definition nullable_nterm (nt:nonterminal) : bool :=
  match nt with
  | term'nt => false
  | quantifier'nt => false
  | patterncharacter'nt => false
  | pattern'nt => true
  | main'nt => false
  | disjunction'nt => true
  | decimaldigits_'nt => false
  | decimaldigits'nt => false
  | decimaldigit'nt => false
  | atom'nt => false
  | assertion'nt => false
  | alternative'nt => true
  end.

Definition first_nterm (nt:nonterminal) : list terminal :=
  match nt with
  | term'nt => [ZERO't; UPW't; UPS't; UPP't; UPD't; UPB't; RBRACK't; RBRAC't; NZDIGIT't; MORE't; MINUS't; LPAR't; LOWX't; LOWW't; LOWV't; LOWU't; LOWT't; LOWS't; LOWR't; LOWP't; LOWN't; LOWK't; LOWF't; LOWD't; LOWB't; LESS't; LBRACK't; LBRAC't; EXCL't; EQUAL't; DOT't; COMMA't; COLONS't; CHAR't]%list
  | quantifier'nt => [STAR't; QMARK't; PLUS't; LBRAC't]%list
  | patterncharacter'nt => [ZERO't; UPW't; UPS't; UPP't; UPD't; UPB't; RBRACK't; RBRAC't; NZDIGIT't; MORE't; MINUS't; LOWX't; LOWW't; LOWV't; LOWU't; LOWT't; LOWS't; LOWR't; LOWP't; LOWN't; LOWK't; LOWF't; LOWD't; LOWB't; LESS't; LBRACK't; LBRAC't; EXCL't; EQUAL't; COMMA't; COLONS't; CHAR't]%list
  | pattern'nt => [ZERO't; UPW't; UPS't; UPP't; UPD't; UPB't; RBRACK't; RBRAC't; NZDIGIT't; MORE't; MINUS't; LPAR't; LOWX't; LOWW't; LOWV't; LOWU't; LOWT't; LOWS't; LOWR't; LOWP't; LOWN't; LOWK't; LOWF't; LOWD't; LOWB't; LESS't; LBRACK't; LBRAC't; EXCL't; EQUAL't; DOT't; COMMA't; COLONS't; CHAR't; ALT't]%list
  | main'nt => [ZERO't; UPW't; UPS't; UPP't; UPD't; UPB't; RBRACK't; RBRAC't; NZDIGIT't; MORE't; MINUS't; LPAR't; LOWX't; LOWW't; LOWV't; LOWU't; LOWT't; LOWS't; LOWR't; LOWP't; LOWN't; LOWK't; LOWF't; LOWD't; LOWB't; LESS't; LBRACK't; LBRAC't; EXCL't; EQUAL't; EOF't; DOT't; COMMA't; COLONS't; CHAR't; ALT't]%list
  | disjunction'nt => [ZERO't; UPW't; UPS't; UPP't; UPD't; UPB't; RBRACK't; RBRAC't; NZDIGIT't; MORE't; MINUS't; LPAR't; LOWX't; LOWW't; LOWV't; LOWU't; LOWT't; LOWS't; LOWR't; LOWP't; LOWN't; LOWK't; LOWF't; LOWD't; LOWB't; LESS't; LBRACK't; LBRAC't; EXCL't; EQUAL't; DOT't; COMMA't; COLONS't; CHAR't; ALT't]%list
  | decimaldigits_'nt => [ZERO't; NZDIGIT't]%list
  | decimaldigits'nt => [ZERO't; NZDIGIT't]%list
  | decimaldigit'nt => [ZERO't; NZDIGIT't]%list
  | atom'nt => [ZERO't; UPW't; UPS't; UPP't; UPD't; UPB't; RBRACK't; RBRAC't; NZDIGIT't; MORE't; MINUS't; LOWX't; LOWW't; LOWV't; LOWU't; LOWT't; LOWS't; LOWR't; LOWP't; LOWN't; LOWK't; LOWF't; LOWD't; LOWB't; LESS't; LBRACK't; LBRAC't; EXCL't; EQUAL't; DOT't; COMMA't; COLONS't; CHAR't]%list
  | assertion'nt => [LPAR't]%list
  | alternative'nt => [ZERO't; UPW't; UPS't; UPP't; UPD't; UPB't; RBRACK't; RBRAC't; NZDIGIT't; MORE't; MINUS't; LPAR't; LOWX't; LOWW't; LOWV't; LOWU't; LOWT't; LOWS't; LOWR't; LOWP't; LOWN't; LOWK't; LOWF't; LOWD't; LOWB't; LESS't; LBRACK't; LBRAC't; EXCL't; EQUAL't; DOT't; COMMA't; COLONS't; CHAR't]%list
  end.

Inductive noninitstate' : Set :=
| Nis'81
| Nis'79
| Nis'78
| Nis'77
| Nis'76
| Nis'75
| Nis'74
| Nis'73
| Nis'72
| Nis'71
| Nis'70
| Nis'69
| Nis'68
| Nis'67
| Nis'66
| Nis'65
| Nis'64
| Nis'63
| Nis'62
| Nis'61
| Nis'60
| Nis'59
| Nis'58
| Nis'57
| Nis'56
| Nis'55
| Nis'54
| Nis'53
| Nis'52
| Nis'51
| Nis'50
| Nis'49
| Nis'48
| Nis'47
| Nis'46
| Nis'45
| Nis'44
| Nis'43
| Nis'42
| Nis'41
| Nis'40
| Nis'39
| Nis'38
| Nis'37
| Nis'36
| Nis'35
| Nis'34
| Nis'33
| Nis'32
| Nis'31
| Nis'30
| Nis'29
| Nis'28
| Nis'27
| Nis'26
| Nis'25
| Nis'24
| Nis'23
| Nis'22
| Nis'21
| Nis'20
| Nis'19
| Nis'18
| Nis'17
| Nis'16
| Nis'15
| Nis'14
| Nis'13
| Nis'12
| Nis'11
| Nis'10
| Nis'9
| Nis'8
| Nis'7
| Nis'6
| Nis'5
| Nis'4
| Nis'3
| Nis'2
| Nis'1.
Definition noninitstate := noninitstate'.

Global Program Instance noninitstateNum : MenhirLib.Alphabet.Numbered noninitstate :=
  { inj := fun x => match x return _ with
    | Nis'81 => 1%positive
    | Nis'79 => 2%positive
    | Nis'78 => 3%positive
    | Nis'77 => 4%positive
    | Nis'76 => 5%positive
    | Nis'75 => 6%positive
    | Nis'74 => 7%positive
    | Nis'73 => 8%positive
    | Nis'72 => 9%positive
    | Nis'71 => 10%positive
    | Nis'70 => 11%positive
    | Nis'69 => 12%positive
    | Nis'68 => 13%positive
    | Nis'67 => 14%positive
    | Nis'66 => 15%positive
    | Nis'65 => 16%positive
    | Nis'64 => 17%positive
    | Nis'63 => 18%positive
    | Nis'62 => 19%positive
    | Nis'61 => 20%positive
    | Nis'60 => 21%positive
    | Nis'59 => 22%positive
    | Nis'58 => 23%positive
    | Nis'57 => 24%positive
    | Nis'56 => 25%positive
    | Nis'55 => 26%positive
    | Nis'54 => 27%positive
    | Nis'53 => 28%positive
    | Nis'52 => 29%positive
    | Nis'51 => 30%positive
    | Nis'50 => 31%positive
    | Nis'49 => 32%positive
    | Nis'48 => 33%positive
    | Nis'47 => 34%positive
    | Nis'46 => 35%positive
    | Nis'45 => 36%positive
    | Nis'44 => 37%positive
    | Nis'43 => 38%positive
    | Nis'42 => 39%positive
    | Nis'41 => 40%positive
    | Nis'40 => 41%positive
    | Nis'39 => 42%positive
    | Nis'38 => 43%positive
    | Nis'37 => 44%positive
    | Nis'36 => 45%positive
    | Nis'35 => 46%positive
    | Nis'34 => 47%positive
    | Nis'33 => 48%positive
    | Nis'32 => 49%positive
    | Nis'31 => 50%positive
    | Nis'30 => 51%positive
    | Nis'29 => 52%positive
    | Nis'28 => 53%positive
    | Nis'27 => 54%positive
    | Nis'26 => 55%positive
    | Nis'25 => 56%positive
    | Nis'24 => 57%positive
    | Nis'23 => 58%positive
    | Nis'22 => 59%positive
    | Nis'21 => 60%positive
    | Nis'20 => 61%positive
    | Nis'19 => 62%positive
    | Nis'18 => 63%positive
    | Nis'17 => 64%positive
    | Nis'16 => 65%positive
    | Nis'15 => 66%positive
    | Nis'14 => 67%positive
    | Nis'13 => 68%positive
    | Nis'12 => 69%positive
    | Nis'11 => 70%positive
    | Nis'10 => 71%positive
    | Nis'9 => 72%positive
    | Nis'8 => 73%positive
    | Nis'7 => 74%positive
    | Nis'6 => 75%positive
    | Nis'5 => 76%positive
    | Nis'4 => 77%positive
    | Nis'3 => 78%positive
    | Nis'2 => 79%positive
    | Nis'1 => 80%positive
    end;
    surj := (fun n => match n return _ with
    | 1%positive => Nis'81
    | 2%positive => Nis'79
    | 3%positive => Nis'78
    | 4%positive => Nis'77
    | 5%positive => Nis'76
    | 6%positive => Nis'75
    | 7%positive => Nis'74
    | 8%positive => Nis'73
    | 9%positive => Nis'72
    | 10%positive => Nis'71
    | 11%positive => Nis'70
    | 12%positive => Nis'69
    | 13%positive => Nis'68
    | 14%positive => Nis'67
    | 15%positive => Nis'66
    | 16%positive => Nis'65
    | 17%positive => Nis'64
    | 18%positive => Nis'63
    | 19%positive => Nis'62
    | 20%positive => Nis'61
    | 21%positive => Nis'60
    | 22%positive => Nis'59
    | 23%positive => Nis'58
    | 24%positive => Nis'57
    | 25%positive => Nis'56
    | 26%positive => Nis'55
    | 27%positive => Nis'54
    | 28%positive => Nis'53
    | 29%positive => Nis'52
    | 30%positive => Nis'51
    | 31%positive => Nis'50
    | 32%positive => Nis'49
    | 33%positive => Nis'48
    | 34%positive => Nis'47
    | 35%positive => Nis'46
    | 36%positive => Nis'45
    | 37%positive => Nis'44
    | 38%positive => Nis'43
    | 39%positive => Nis'42
    | 40%positive => Nis'41
    | 41%positive => Nis'40
    | 42%positive => Nis'39
    | 43%positive => Nis'38
    | 44%positive => Nis'37
    | 45%positive => Nis'36
    | 46%positive => Nis'35
    | 47%positive => Nis'34
    | 48%positive => Nis'33
    | 49%positive => Nis'32
    | 50%positive => Nis'31
    | 51%positive => Nis'30
    | 52%positive => Nis'29
    | 53%positive => Nis'28
    | 54%positive => Nis'27
    | 55%positive => Nis'26
    | 56%positive => Nis'25
    | 57%positive => Nis'24
    | 58%positive => Nis'23
    | 59%positive => Nis'22
    | 60%positive => Nis'21
    | 61%positive => Nis'20
    | 62%positive => Nis'19
    | 63%positive => Nis'18
    | 64%positive => Nis'17
    | 65%positive => Nis'16
    | 66%positive => Nis'15
    | 67%positive => Nis'14
    | 68%positive => Nis'13
    | 69%positive => Nis'12
    | 70%positive => Nis'11
    | 71%positive => Nis'10
    | 72%positive => Nis'9
    | 73%positive => Nis'8
    | 74%positive => Nis'7
    | 75%positive => Nis'6
    | 76%positive => Nis'5
    | 77%positive => Nis'4
    | 78%positive => Nis'3
    | 79%positive => Nis'2
    | 80%positive => Nis'1
    | _ => Nis'81
    end)%Z;
    inj_bound := 80%positive }.
Global Instance NonInitStateAlph : MenhirLib.Alphabet.Alphabet noninitstate := _.

Definition last_symb_of_non_init_state (noninitstate:noninitstate) : symbol :=
  match noninitstate with
  | Nis'1 => T ZERO't
  | Nis'2 => T UPW't
  | Nis'3 => T UPS't
  | Nis'4 => T UPP't
  | Nis'5 => T UPD't
  | Nis'6 => T UPB't
  | Nis'7 => T RBRACK't
  | Nis'8 => T RBRAC't
  | Nis'9 => T NZDIGIT't
  | Nis'10 => T MORE't
  | Nis'11 => T MINUS't
  | Nis'12 => T LPAR't
  | Nis'13 => T QMARK't
  | Nis'14 => T LESS't
  | Nis'15 => T EXCL't
  | Nis'16 => T LOWX't
  | Nis'17 => T LOWW't
  | Nis'18 => T LOWV't
  | Nis'19 => T LOWU't
  | Nis'20 => T LOWT't
  | Nis'21 => T LOWS't
  | Nis'22 => T LOWR't
  | Nis'23 => T LOWP't
  | Nis'24 => T LOWN't
  | Nis'25 => T LOWK't
  | Nis'26 => T LOWF't
  | Nis'27 => T LOWD't
  | Nis'28 => T LOWB't
  | Nis'29 => T LESS't
  | Nis'30 => T LBRACK't
  | Nis'31 => T LBRAC't
  | Nis'32 => T EXCL't
  | Nis'33 => T EQUAL't
  | Nis'34 => T DOT't
  | Nis'35 => T COMMA't
  | Nis'36 => T COLONS't
  | Nis'37 => T CHAR't
  | Nis'38 => NT term'nt
  | Nis'39 => NT patterncharacter'nt
  | Nis'40 => NT disjunction'nt
  | Nis'41 => T RPAR't
  | Nis'42 => NT decimaldigit'nt
  | Nis'43 => NT atom'nt
  | Nis'44 => T STAR't
  | Nis'45 => T QMARK't
  | Nis'46 => T QMARK't
  | Nis'47 => T QMARK't
  | Nis'48 => T PLUS't
  | Nis'49 => T QMARK't
  | Nis'50 => T LBRAC't
  | Nis'51 => NT decimaldigits_'nt
  | Nis'52 => NT decimaldigit'nt
  | Nis'53 => NT decimaldigits'nt
  | Nis'54 => T RBRAC't
  | Nis'55 => T QMARK't
  | Nis'56 => T COMMA't
  | Nis'57 => T RBRAC't
  | Nis'58 => T QMARK't
  | Nis'59 => NT decimaldigits'nt
  | Nis'60 => T RBRAC't
  | Nis'61 => T QMARK't
  | Nis'62 => NT decimaldigit'nt
  | Nis'63 => NT quantifier'nt
  | Nis'64 => NT assertion'nt
  | Nis'65 => NT alternative'nt
  | Nis'66 => T ALT't
  | Nis'67 => NT disjunction'nt
  | Nis'68 => NT term'nt
  | Nis'69 => T EQUAL't
  | Nis'70 => NT disjunction'nt
  | Nis'71 => T RPAR't
  | Nis'72 => T EXCL't
  | Nis'73 => NT disjunction'nt
  | Nis'74 => T RPAR't
  | Nis'75 => T EQUAL't
  | Nis'76 => NT disjunction'nt
  | Nis'77 => T RPAR't
  | Nis'78 => NT pattern'nt
  | Nis'79 => T EOF't
  | Nis'81 => NT disjunction'nt
  end.

Inductive initstate' : Set :=
| Init'0.
Definition initstate := initstate'.

Global Program Instance initstateNum : MenhirLib.Alphabet.Numbered initstate :=
  { inj := fun x => match x return _ with
    | Init'0 => 1%positive
    end;
    surj := (fun n => match n return _ with
    | 1%positive => Init'0
    | _ => Init'0
    end)%Z;
    inj_bound := 1%positive }.
Global Instance InitStateAlph : MenhirLib.Alphabet.Alphabet initstate := _.

Include MenhirLib.Automaton.Types.

Definition start_nt (init:initstate) : nonterminal :=
  match init with
  | Init'0 => main'nt
  end.

Definition action_table (state:state) : action :=
  match state with
  | Init Init'0 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | ZERO't => Shift_act Nis'1 (eq_refl _)
    | UPW't => Shift_act Nis'2 (eq_refl _)
    | UPS't => Shift_act Nis'3 (eq_refl _)
    | UPP't => Shift_act Nis'4 (eq_refl _)
    | UPD't => Shift_act Nis'5 (eq_refl _)
    | UPB't => Shift_act Nis'6 (eq_refl _)
    | RBRACK't => Shift_act Nis'7 (eq_refl _)
    | RBRAC't => Shift_act Nis'8 (eq_refl _)
    | NZDIGIT't => Shift_act Nis'9 (eq_refl _)
    | MORE't => Shift_act Nis'10 (eq_refl _)
    | MINUS't => Shift_act Nis'11 (eq_refl _)
    | LPAR't => Shift_act Nis'12 (eq_refl _)
    | LOWX't => Shift_act Nis'16 (eq_refl _)
    | LOWW't => Shift_act Nis'17 (eq_refl _)
    | LOWV't => Shift_act Nis'18 (eq_refl _)
    | LOWU't => Shift_act Nis'19 (eq_refl _)
    | LOWT't => Shift_act Nis'20 (eq_refl _)
    | LOWS't => Shift_act Nis'21 (eq_refl _)
    | LOWR't => Shift_act Nis'22 (eq_refl _)
    | LOWP't => Shift_act Nis'23 (eq_refl _)
    | LOWN't => Shift_act Nis'24 (eq_refl _)
    | LOWK't => Shift_act Nis'25 (eq_refl _)
    | LOWF't => Shift_act Nis'26 (eq_refl _)
    | LOWD't => Shift_act Nis'27 (eq_refl _)
    | LOWB't => Shift_act Nis'28 (eq_refl _)
    | LESS't => Shift_act Nis'29 (eq_refl _)
    | LBRACK't => Shift_act Nis'30 (eq_refl _)
    | LBRAC't => Shift_act Nis'31 (eq_refl _)
    | EXCL't => Shift_act Nis'32 (eq_refl _)
    | EQUAL't => Shift_act Nis'33 (eq_refl _)
    | EOF't => Reduce_act Prod'alternative'2
    | DOT't => Shift_act Nis'34 (eq_refl _)
    | COMMA't => Shift_act Nis'35 (eq_refl _)
    | COLONS't => Shift_act Nis'36 (eq_refl _)
    | CHAR't => Shift_act Nis'37 (eq_refl _)
    | ALT't => Reduce_act Prod'alternative'2
    | _ => Fail_act
    end)
  | Ninit Nis'1 => Default_reduce_act Prod'decimaldigit'1
  | Ninit Nis'2 => Default_reduce_act Prod'patterncharacter'8
  | Ninit Nis'3 => Default_reduce_act Prod'patterncharacter'6
  | Ninit Nis'4 => Default_reduce_act Prod'patterncharacter'18
  | Ninit Nis'5 => Default_reduce_act Prod'patterncharacter'4
  | Ninit Nis'6 => Default_reduce_act Prod'patterncharacter'2
  | Ninit Nis'7 => Default_reduce_act Prod'patterncharacter'29
  | Ninit Nis'8 => Default_reduce_act Prod'patterncharacter'27
  | Ninit Nis'9 => Default_reduce_act Prod'decimaldigit'0
  | Ninit Nis'10 => Default_reduce_act Prod'patterncharacter'22
  | Ninit Nis'11 => Default_reduce_act Prod'patterncharacter'24
  | Ninit Nis'12 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | QMARK't => Shift_act Nis'13 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'13 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | LESS't => Shift_act Nis'14 (eq_refl _)
    | EXCL't => Shift_act Nis'72 (eq_refl _)
    | EQUAL't => Shift_act Nis'75 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'14 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | EXCL't => Shift_act Nis'15 (eq_refl _)
    | EQUAL't => Shift_act Nis'69 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'15 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | ZERO't => Shift_act Nis'1 (eq_refl _)
    | UPW't => Shift_act Nis'2 (eq_refl _)
    | UPS't => Shift_act Nis'3 (eq_refl _)
    | UPP't => Shift_act Nis'4 (eq_refl _)
    | UPD't => Shift_act Nis'5 (eq_refl _)
    | UPB't => Shift_act Nis'6 (eq_refl _)
    | RPAR't => Reduce_act Prod'alternative'2
    | RBRACK't => Shift_act Nis'7 (eq_refl _)
    | RBRAC't => Shift_act Nis'8 (eq_refl _)
    | NZDIGIT't => Shift_act Nis'9 (eq_refl _)
    | MORE't => Shift_act Nis'10 (eq_refl _)
    | MINUS't => Shift_act Nis'11 (eq_refl _)
    | LPAR't => Shift_act Nis'12 (eq_refl _)
    | LOWX't => Shift_act Nis'16 (eq_refl _)
    | LOWW't => Shift_act Nis'17 (eq_refl _)
    | LOWV't => Shift_act Nis'18 (eq_refl _)
    | LOWU't => Shift_act Nis'19 (eq_refl _)
    | LOWT't => Shift_act Nis'20 (eq_refl _)
    | LOWS't => Shift_act Nis'21 (eq_refl _)
    | LOWR't => Shift_act Nis'22 (eq_refl _)
    | LOWP't => Shift_act Nis'23 (eq_refl _)
    | LOWN't => Shift_act Nis'24 (eq_refl _)
    | LOWK't => Shift_act Nis'25 (eq_refl _)
    | LOWF't => Shift_act Nis'26 (eq_refl _)
    | LOWD't => Shift_act Nis'27 (eq_refl _)
    | LOWB't => Shift_act Nis'28 (eq_refl _)
    | LESS't => Shift_act Nis'29 (eq_refl _)
    | LBRACK't => Shift_act Nis'30 (eq_refl _)
    | LBRAC't => Shift_act Nis'31 (eq_refl _)
    | EXCL't => Shift_act Nis'32 (eq_refl _)
    | EQUAL't => Shift_act Nis'33 (eq_refl _)
    | DOT't => Shift_act Nis'34 (eq_refl _)
    | COMMA't => Shift_act Nis'35 (eq_refl _)
    | COLONS't => Shift_act Nis'36 (eq_refl _)
    | CHAR't => Shift_act Nis'37 (eq_refl _)
    | ALT't => Reduce_act Prod'alternative'2
    | _ => Fail_act
    end)
  | Ninit Nis'16 => Default_reduce_act Prod'patterncharacter'15
  | Ninit Nis'17 => Default_reduce_act Prod'patterncharacter'7
  | Ninit Nis'18 => Default_reduce_act Prod'patterncharacter'13
  | Ninit Nis'19 => Default_reduce_act Prod'patterncharacter'16
  | Ninit Nis'20 => Default_reduce_act Prod'patterncharacter'12
  | Ninit Nis'21 => Default_reduce_act Prod'patterncharacter'5
  | Ninit Nis'22 => Default_reduce_act Prod'patterncharacter'11
  | Ninit Nis'23 => Default_reduce_act Prod'patterncharacter'17
  | Ninit Nis'24 => Default_reduce_act Prod'patterncharacter'10
  | Ninit Nis'25 => Default_reduce_act Prod'patterncharacter'14
  | Ninit Nis'26 => Default_reduce_act Prod'patterncharacter'9
  | Ninit Nis'27 => Default_reduce_act Prod'patterncharacter'3
  | Ninit Nis'28 => Default_reduce_act Prod'patterncharacter'1
  | Ninit Nis'29 => Default_reduce_act Prod'patterncharacter'21
  | Ninit Nis'30 => Default_reduce_act Prod'patterncharacter'28
  | Ninit Nis'31 => Default_reduce_act Prod'patterncharacter'26
  | Ninit Nis'32 => Default_reduce_act Prod'patterncharacter'25
  | Ninit Nis'33 => Default_reduce_act Prod'patterncharacter'23
  | Ninit Nis'34 => Default_reduce_act Prod'atom'1
  | Ninit Nis'35 => Default_reduce_act Prod'patterncharacter'19
  | Ninit Nis'36 => Default_reduce_act Prod'patterncharacter'20
  | Ninit Nis'37 => Default_reduce_act Prod'patterncharacter'0
  | Ninit Nis'38 => Default_reduce_act Prod'alternative'1
  | Ninit Nis'39 => Default_reduce_act Prod'atom'0
  | Ninit Nis'40 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | RPAR't => Shift_act Nis'41 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'41 => Default_reduce_act Prod'assertion'3
  | Ninit Nis'42 => Default_reduce_act Prod'patterncharacter'30
  | Ninit Nis'43 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | ZERO't => Reduce_act Prod'term'1
    | UPW't => Reduce_act Prod'term'1
    | UPS't => Reduce_act Prod'term'1
    | UPP't => Reduce_act Prod'term'1
    | UPD't => Reduce_act Prod'term'1
    | UPB't => Reduce_act Prod'term'1
    | STAR't => Shift_act Nis'44 (eq_refl _)
    | RPAR't => Reduce_act Prod'term'1
    | RBRACK't => Reduce_act Prod'term'1
    | RBRAC't => Reduce_act Prod'term'1
    | QMARK't => Shift_act Nis'46 (eq_refl _)
    | PLUS't => Shift_act Nis'48 (eq_refl _)
    | NZDIGIT't => Reduce_act Prod'term'1
    | MORE't => Reduce_act Prod'term'1
    | MINUS't => Reduce_act Prod'term'1
    | LPAR't => Reduce_act Prod'term'1
    | LOWX't => Reduce_act Prod'term'1
    | LOWW't => Reduce_act Prod'term'1
    | LOWV't => Reduce_act Prod'term'1
    | LOWU't => Reduce_act Prod'term'1
    | LOWT't => Reduce_act Prod'term'1
    | LOWS't => Reduce_act Prod'term'1
    | LOWR't => Reduce_act Prod'term'1
    | LOWP't => Reduce_act Prod'term'1
    | LOWN't => Reduce_act Prod'term'1
    | LOWK't => Reduce_act Prod'term'1
    | LOWF't => Reduce_act Prod'term'1
    | LOWD't => Reduce_act Prod'term'1
    | LOWB't => Reduce_act Prod'term'1
    | LESS't => Reduce_act Prod'term'1
    | LBRACK't => Reduce_act Prod'term'1
    | LBRAC't => Shift_act Nis'50 (eq_refl _)
    | EXCL't => Reduce_act Prod'term'1
    | EQUAL't => Reduce_act Prod'term'1
    | EOF't => Reduce_act Prod'term'1
    | DOT't => Reduce_act Prod'term'1
    | COMMA't => Reduce_act Prod'term'1
    | COLONS't => Reduce_act Prod'term'1
    | CHAR't => Reduce_act Prod'term'1
    | ALT't => Reduce_act Prod'term'1
    | _ => Fail_act
    end)
  | Ninit Nis'44 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | ZERO't => Reduce_act Prod'quantifier'0
    | UPW't => Reduce_act Prod'quantifier'0
    | UPS't => Reduce_act Prod'quantifier'0
    | UPP't => Reduce_act Prod'quantifier'0
    | UPD't => Reduce_act Prod'quantifier'0
    | UPB't => Reduce_act Prod'quantifier'0
    | RPAR't => Reduce_act Prod'quantifier'0
    | RBRACK't => Reduce_act Prod'quantifier'0
    | RBRAC't => Reduce_act Prod'quantifier'0
    | QMARK't => Shift_act Nis'45 (eq_refl _)
    | NZDIGIT't => Reduce_act Prod'quantifier'0
    | MORE't => Reduce_act Prod'quantifier'0
    | MINUS't => Reduce_act Prod'quantifier'0
    | LPAR't => Reduce_act Prod'quantifier'0
    | LOWX't => Reduce_act Prod'quantifier'0
    | LOWW't => Reduce_act Prod'quantifier'0
    | LOWV't => Reduce_act Prod'quantifier'0
    | LOWU't => Reduce_act Prod'quantifier'0
    | LOWT't => Reduce_act Prod'quantifier'0
    | LOWS't => Reduce_act Prod'quantifier'0
    | LOWR't => Reduce_act Prod'quantifier'0
    | LOWP't => Reduce_act Prod'quantifier'0
    | LOWN't => Reduce_act Prod'quantifier'0
    | LOWK't => Reduce_act Prod'quantifier'0
    | LOWF't => Reduce_act Prod'quantifier'0
    | LOWD't => Reduce_act Prod'quantifier'0
    | LOWB't => Reduce_act Prod'quantifier'0
    | LESS't => Reduce_act Prod'quantifier'0
    | LBRACK't => Reduce_act Prod'quantifier'0
    | LBRAC't => Reduce_act Prod'quantifier'0
    | EXCL't => Reduce_act Prod'quantifier'0
    | EQUAL't => Reduce_act Prod'quantifier'0
    | EOF't => Reduce_act Prod'quantifier'0
    | DOT't => Reduce_act Prod'quantifier'0
    | COMMA't => Reduce_act Prod'quantifier'0
    | COLONS't => Reduce_act Prod'quantifier'0
    | CHAR't => Reduce_act Prod'quantifier'0
    | ALT't => Reduce_act Prod'quantifier'0
    | _ => Fail_act
    end)
  | Ninit Nis'45 => Default_reduce_act Prod'quantifier'1
  | Ninit Nis'46 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | ZERO't => Reduce_act Prod'quantifier'4
    | UPW't => Reduce_act Prod'quantifier'4
    | UPS't => Reduce_act Prod'quantifier'4
    | UPP't => Reduce_act Prod'quantifier'4
    | UPD't => Reduce_act Prod'quantifier'4
    | UPB't => Reduce_act Prod'quantifier'4
    | RPAR't => Reduce_act Prod'quantifier'4
    | RBRACK't => Reduce_act Prod'quantifier'4
    | RBRAC't => Reduce_act Prod'quantifier'4
    | QMARK't => Shift_act Nis'47 (eq_refl _)
    | NZDIGIT't => Reduce_act Prod'quantifier'4
    | MORE't => Reduce_act Prod'quantifier'4
    | MINUS't => Reduce_act Prod'quantifier'4
    | LPAR't => Reduce_act Prod'quantifier'4
    | LOWX't => Reduce_act Prod'quantifier'4
    | LOWW't => Reduce_act Prod'quantifier'4
    | LOWV't => Reduce_act Prod'quantifier'4
    | LOWU't => Reduce_act Prod'quantifier'4
    | LOWT't => Reduce_act Prod'quantifier'4
    | LOWS't => Reduce_act Prod'quantifier'4
    | LOWR't => Reduce_act Prod'quantifier'4
    | LOWP't => Reduce_act Prod'quantifier'4
    | LOWN't => Reduce_act Prod'quantifier'4
    | LOWK't => Reduce_act Prod'quantifier'4
    | LOWF't => Reduce_act Prod'quantifier'4
    | LOWD't => Reduce_act Prod'quantifier'4
    | LOWB't => Reduce_act Prod'quantifier'4
    | LESS't => Reduce_act Prod'quantifier'4
    | LBRACK't => Reduce_act Prod'quantifier'4
    | LBRAC't => Reduce_act Prod'quantifier'4
    | EXCL't => Reduce_act Prod'quantifier'4
    | EQUAL't => Reduce_act Prod'quantifier'4
    | EOF't => Reduce_act Prod'quantifier'4
    | DOT't => Reduce_act Prod'quantifier'4
    | COMMA't => Reduce_act Prod'quantifier'4
    | COLONS't => Reduce_act Prod'quantifier'4
    | CHAR't => Reduce_act Prod'quantifier'4
    | ALT't => Reduce_act Prod'quantifier'4
    | _ => Fail_act
    end)
  | Ninit Nis'47 => Default_reduce_act Prod'quantifier'5
  | Ninit Nis'48 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | ZERO't => Reduce_act Prod'quantifier'2
    | UPW't => Reduce_act Prod'quantifier'2
    | UPS't => Reduce_act Prod'quantifier'2
    | UPP't => Reduce_act Prod'quantifier'2
    | UPD't => Reduce_act Prod'quantifier'2
    | UPB't => Reduce_act Prod'quantifier'2
    | RPAR't => Reduce_act Prod'quantifier'2
    | RBRACK't => Reduce_act Prod'quantifier'2
    | RBRAC't => Reduce_act Prod'quantifier'2
    | QMARK't => Shift_act Nis'49 (eq_refl _)
    | NZDIGIT't => Reduce_act Prod'quantifier'2
    | MORE't => Reduce_act Prod'quantifier'2
    | MINUS't => Reduce_act Prod'quantifier'2
    | LPAR't => Reduce_act Prod'quantifier'2
    | LOWX't => Reduce_act Prod'quantifier'2
    | LOWW't => Reduce_act Prod'quantifier'2
    | LOWV't => Reduce_act Prod'quantifier'2
    | LOWU't => Reduce_act Prod'quantifier'2
    | LOWT't => Reduce_act Prod'quantifier'2
    | LOWS't => Reduce_act Prod'quantifier'2
    | LOWR't => Reduce_act Prod'quantifier'2
    | LOWP't => Reduce_act Prod'quantifier'2
    | LOWN't => Reduce_act Prod'quantifier'2
    | LOWK't => Reduce_act Prod'quantifier'2
    | LOWF't => Reduce_act Prod'quantifier'2
    | LOWD't => Reduce_act Prod'quantifier'2
    | LOWB't => Reduce_act Prod'quantifier'2
    | LESS't => Reduce_act Prod'quantifier'2
    | LBRACK't => Reduce_act Prod'quantifier'2
    | LBRAC't => Reduce_act Prod'quantifier'2
    | EXCL't => Reduce_act Prod'quantifier'2
    | EQUAL't => Reduce_act Prod'quantifier'2
    | EOF't => Reduce_act Prod'quantifier'2
    | DOT't => Reduce_act Prod'quantifier'2
    | COMMA't => Reduce_act Prod'quantifier'2
    | COLONS't => Reduce_act Prod'quantifier'2
    | CHAR't => Reduce_act Prod'quantifier'2
    | ALT't => Reduce_act Prod'quantifier'2
    | _ => Fail_act
    end)
  | Ninit Nis'49 => Default_reduce_act Prod'quantifier'3
  | Ninit Nis'50 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | ZERO't => Shift_act Nis'1 (eq_refl _)
    | NZDIGIT't => Shift_act Nis'9 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'51 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | ZERO't => Shift_act Nis'1 (eq_refl _)
    | RBRAC't => Reduce_act Prod'decimaldigits'0
    | NZDIGIT't => Shift_act Nis'9 (eq_refl _)
    | COMMA't => Reduce_act Prod'decimaldigits'0
    | _ => Fail_act
    end)
  | Ninit Nis'52 => Default_reduce_act Prod'decimaldigits_'0
  | Ninit Nis'53 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | RBRAC't => Shift_act Nis'54 (eq_refl _)
    | COMMA't => Shift_act Nis'56 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'54 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | ZERO't => Reduce_act Prod'quantifier'6
    | UPW't => Reduce_act Prod'quantifier'6
    | UPS't => Reduce_act Prod'quantifier'6
    | UPP't => Reduce_act Prod'quantifier'6
    | UPD't => Reduce_act Prod'quantifier'6
    | UPB't => Reduce_act Prod'quantifier'6
    | RPAR't => Reduce_act Prod'quantifier'6
    | RBRACK't => Reduce_act Prod'quantifier'6
    | RBRAC't => Reduce_act Prod'quantifier'6
    | QMARK't => Shift_act Nis'55 (eq_refl _)
    | NZDIGIT't => Reduce_act Prod'quantifier'6
    | MORE't => Reduce_act Prod'quantifier'6
    | MINUS't => Reduce_act Prod'quantifier'6
    | LPAR't => Reduce_act Prod'quantifier'6
    | LOWX't => Reduce_act Prod'quantifier'6
    | LOWW't => Reduce_act Prod'quantifier'6
    | LOWV't => Reduce_act Prod'quantifier'6
    | LOWU't => Reduce_act Prod'quantifier'6
    | LOWT't => Reduce_act Prod'quantifier'6
    | LOWS't => Reduce_act Prod'quantifier'6
    | LOWR't => Reduce_act Prod'quantifier'6
    | LOWP't => Reduce_act Prod'quantifier'6
    | LOWN't => Reduce_act Prod'quantifier'6
    | LOWK't => Reduce_act Prod'quantifier'6
    | LOWF't => Reduce_act Prod'quantifier'6
    | LOWD't => Reduce_act Prod'quantifier'6
    | LOWB't => Reduce_act Prod'quantifier'6
    | LESS't => Reduce_act Prod'quantifier'6
    | LBRACK't => Reduce_act Prod'quantifier'6
    | LBRAC't => Reduce_act Prod'quantifier'6
    | EXCL't => Reduce_act Prod'quantifier'6
    | EQUAL't => Reduce_act Prod'quantifier'6
    | EOF't => Reduce_act Prod'quantifier'6
    | DOT't => Reduce_act Prod'quantifier'6
    | COMMA't => Reduce_act Prod'quantifier'6
    | COLONS't => Reduce_act Prod'quantifier'6
    | CHAR't => Reduce_act Prod'quantifier'6
    | ALT't => Reduce_act Prod'quantifier'6
    | _ => Fail_act
    end)
  | Ninit Nis'55 => Default_reduce_act Prod'quantifier'7
  | Ninit Nis'56 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | ZERO't => Shift_act Nis'1 (eq_refl _)
    | RBRAC't => Shift_act Nis'57 (eq_refl _)
    | NZDIGIT't => Shift_act Nis'9 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'57 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | ZERO't => Reduce_act Prod'quantifier'8
    | UPW't => Reduce_act Prod'quantifier'8
    | UPS't => Reduce_act Prod'quantifier'8
    | UPP't => Reduce_act Prod'quantifier'8
    | UPD't => Reduce_act Prod'quantifier'8
    | UPB't => Reduce_act Prod'quantifier'8
    | RPAR't => Reduce_act Prod'quantifier'8
    | RBRACK't => Reduce_act Prod'quantifier'8
    | RBRAC't => Reduce_act Prod'quantifier'8
    | QMARK't => Shift_act Nis'58 (eq_refl _)
    | NZDIGIT't => Reduce_act Prod'quantifier'8
    | MORE't => Reduce_act Prod'quantifier'8
    | MINUS't => Reduce_act Prod'quantifier'8
    | LPAR't => Reduce_act Prod'quantifier'8
    | LOWX't => Reduce_act Prod'quantifier'8
    | LOWW't => Reduce_act Prod'quantifier'8
    | LOWV't => Reduce_act Prod'quantifier'8
    | LOWU't => Reduce_act Prod'quantifier'8
    | LOWT't => Reduce_act Prod'quantifier'8
    | LOWS't => Reduce_act Prod'quantifier'8
    | LOWR't => Reduce_act Prod'quantifier'8
    | LOWP't => Reduce_act Prod'quantifier'8
    | LOWN't => Reduce_act Prod'quantifier'8
    | LOWK't => Reduce_act Prod'quantifier'8
    | LOWF't => Reduce_act Prod'quantifier'8
    | LOWD't => Reduce_act Prod'quantifier'8
    | LOWB't => Reduce_act Prod'quantifier'8
    | LESS't => Reduce_act Prod'quantifier'8
    | LBRACK't => Reduce_act Prod'quantifier'8
    | LBRAC't => Reduce_act Prod'quantifier'8
    | EXCL't => Reduce_act Prod'quantifier'8
    | EQUAL't => Reduce_act Prod'quantifier'8
    | EOF't => Reduce_act Prod'quantifier'8
    | DOT't => Reduce_act Prod'quantifier'8
    | COMMA't => Reduce_act Prod'quantifier'8
    | COLONS't => Reduce_act Prod'quantifier'8
    | CHAR't => Reduce_act Prod'quantifier'8
    | ALT't => Reduce_act Prod'quantifier'8
    | _ => Fail_act
    end)
  | Ninit Nis'58 => Default_reduce_act Prod'quantifier'9
  | Ninit Nis'59 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | RBRAC't => Shift_act Nis'60 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'60 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | ZERO't => Reduce_act Prod'quantifier'10
    | UPW't => Reduce_act Prod'quantifier'10
    | UPS't => Reduce_act Prod'quantifier'10
    | UPP't => Reduce_act Prod'quantifier'10
    | UPD't => Reduce_act Prod'quantifier'10
    | UPB't => Reduce_act Prod'quantifier'10
    | RPAR't => Reduce_act Prod'quantifier'10
    | RBRACK't => Reduce_act Prod'quantifier'10
    | RBRAC't => Reduce_act Prod'quantifier'10
    | QMARK't => Shift_act Nis'61 (eq_refl _)
    | NZDIGIT't => Reduce_act Prod'quantifier'10
    | MORE't => Reduce_act Prod'quantifier'10
    | MINUS't => Reduce_act Prod'quantifier'10
    | LPAR't => Reduce_act Prod'quantifier'10
    | LOWX't => Reduce_act Prod'quantifier'10
    | LOWW't => Reduce_act Prod'quantifier'10
    | LOWV't => Reduce_act Prod'quantifier'10
    | LOWU't => Reduce_act Prod'quantifier'10
    | LOWT't => Reduce_act Prod'quantifier'10
    | LOWS't => Reduce_act Prod'quantifier'10
    | LOWR't => Reduce_act Prod'quantifier'10
    | LOWP't => Reduce_act Prod'quantifier'10
    | LOWN't => Reduce_act Prod'quantifier'10
    | LOWK't => Reduce_act Prod'quantifier'10
    | LOWF't => Reduce_act Prod'quantifier'10
    | LOWD't => Reduce_act Prod'quantifier'10
    | LOWB't => Reduce_act Prod'quantifier'10
    | LESS't => Reduce_act Prod'quantifier'10
    | LBRACK't => Reduce_act Prod'quantifier'10
    | LBRAC't => Reduce_act Prod'quantifier'10
    | EXCL't => Reduce_act Prod'quantifier'10
    | EQUAL't => Reduce_act Prod'quantifier'10
    | EOF't => Reduce_act Prod'quantifier'10
    | DOT't => Reduce_act Prod'quantifier'10
    | COMMA't => Reduce_act Prod'quantifier'10
    | COLONS't => Reduce_act Prod'quantifier'10
    | CHAR't => Reduce_act Prod'quantifier'10
    | ALT't => Reduce_act Prod'quantifier'10
    | _ => Fail_act
    end)
  | Ninit Nis'61 => Default_reduce_act Prod'quantifier'11
  | Ninit Nis'62 => Default_reduce_act Prod'decimaldigits_'1
  | Ninit Nis'63 => Default_reduce_act Prod'term'2
  | Ninit Nis'64 => Default_reduce_act Prod'term'0
  | Ninit Nis'65 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | ZERO't => Shift_act Nis'1 (eq_refl _)
    | UPW't => Shift_act Nis'2 (eq_refl _)
    | UPS't => Shift_act Nis'3 (eq_refl _)
    | UPP't => Shift_act Nis'4 (eq_refl _)
    | UPD't => Shift_act Nis'5 (eq_refl _)
    | UPB't => Shift_act Nis'6 (eq_refl _)
    | RPAR't => Reduce_act Prod'disjunction'0
    | RBRACK't => Shift_act Nis'7 (eq_refl _)
    | RBRAC't => Shift_act Nis'8 (eq_refl _)
    | NZDIGIT't => Shift_act Nis'9 (eq_refl _)
    | MORE't => Shift_act Nis'10 (eq_refl _)
    | MINUS't => Shift_act Nis'11 (eq_refl _)
    | LPAR't => Shift_act Nis'12 (eq_refl _)
    | LOWX't => Shift_act Nis'16 (eq_refl _)
    | LOWW't => Shift_act Nis'17 (eq_refl _)
    | LOWV't => Shift_act Nis'18 (eq_refl _)
    | LOWU't => Shift_act Nis'19 (eq_refl _)
    | LOWT't => Shift_act Nis'20 (eq_refl _)
    | LOWS't => Shift_act Nis'21 (eq_refl _)
    | LOWR't => Shift_act Nis'22 (eq_refl _)
    | LOWP't => Shift_act Nis'23 (eq_refl _)
    | LOWN't => Shift_act Nis'24 (eq_refl _)
    | LOWK't => Shift_act Nis'25 (eq_refl _)
    | LOWF't => Shift_act Nis'26 (eq_refl _)
    | LOWD't => Shift_act Nis'27 (eq_refl _)
    | LOWB't => Shift_act Nis'28 (eq_refl _)
    | LESS't => Shift_act Nis'29 (eq_refl _)
    | LBRACK't => Shift_act Nis'30 (eq_refl _)
    | LBRAC't => Shift_act Nis'31 (eq_refl _)
    | EXCL't => Shift_act Nis'32 (eq_refl _)
    | EQUAL't => Shift_act Nis'33 (eq_refl _)
    | EOF't => Reduce_act Prod'disjunction'0
    | DOT't => Shift_act Nis'34 (eq_refl _)
    | COMMA't => Shift_act Nis'35 (eq_refl _)
    | COLONS't => Shift_act Nis'36 (eq_refl _)
    | CHAR't => Shift_act Nis'37 (eq_refl _)
    | ALT't => Shift_act Nis'66 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'66 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | ZERO't => Shift_act Nis'1 (eq_refl _)
    | UPW't => Shift_act Nis'2 (eq_refl _)
    | UPS't => Shift_act Nis'3 (eq_refl _)
    | UPP't => Shift_act Nis'4 (eq_refl _)
    | UPD't => Shift_act Nis'5 (eq_refl _)
    | UPB't => Shift_act Nis'6 (eq_refl _)
    | RPAR't => Reduce_act Prod'alternative'2
    | RBRACK't => Shift_act Nis'7 (eq_refl _)
    | RBRAC't => Shift_act Nis'8 (eq_refl _)
    | NZDIGIT't => Shift_act Nis'9 (eq_refl _)
    | MORE't => Shift_act Nis'10 (eq_refl _)
    | MINUS't => Shift_act Nis'11 (eq_refl _)
    | LPAR't => Shift_act Nis'12 (eq_refl _)
    | LOWX't => Shift_act Nis'16 (eq_refl _)
    | LOWW't => Shift_act Nis'17 (eq_refl _)
    | LOWV't => Shift_act Nis'18 (eq_refl _)
    | LOWU't => Shift_act Nis'19 (eq_refl _)
    | LOWT't => Shift_act Nis'20 (eq_refl _)
    | LOWS't => Shift_act Nis'21 (eq_refl _)
    | LOWR't => Shift_act Nis'22 (eq_refl _)
    | LOWP't => Shift_act Nis'23 (eq_refl _)
    | LOWN't => Shift_act Nis'24 (eq_refl _)
    | LOWK't => Shift_act Nis'25 (eq_refl _)
    | LOWF't => Shift_act Nis'26 (eq_refl _)
    | LOWD't => Shift_act Nis'27 (eq_refl _)
    | LOWB't => Shift_act Nis'28 (eq_refl _)
    | LESS't => Shift_act Nis'29 (eq_refl _)
    | LBRACK't => Shift_act Nis'30 (eq_refl _)
    | LBRAC't => Shift_act Nis'31 (eq_refl _)
    | EXCL't => Shift_act Nis'32 (eq_refl _)
    | EQUAL't => Shift_act Nis'33 (eq_refl _)
    | EOF't => Reduce_act Prod'alternative'2
    | DOT't => Shift_act Nis'34 (eq_refl _)
    | COMMA't => Shift_act Nis'35 (eq_refl _)
    | COLONS't => Shift_act Nis'36 (eq_refl _)
    | CHAR't => Shift_act Nis'37 (eq_refl _)
    | ALT't => Reduce_act Prod'alternative'2
    | _ => Fail_act
    end)
  | Ninit Nis'67 => Default_reduce_act Prod'disjunction'1
  | Ninit Nis'68 => Default_reduce_act Prod'alternative'0
  | Ninit Nis'69 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | ZERO't => Shift_act Nis'1 (eq_refl _)
    | UPW't => Shift_act Nis'2 (eq_refl _)
    | UPS't => Shift_act Nis'3 (eq_refl _)
    | UPP't => Shift_act Nis'4 (eq_refl _)
    | UPD't => Shift_act Nis'5 (eq_refl _)
    | UPB't => Shift_act Nis'6 (eq_refl _)
    | RPAR't => Reduce_act Prod'alternative'2
    | RBRACK't => Shift_act Nis'7 (eq_refl _)
    | RBRAC't => Shift_act Nis'8 (eq_refl _)
    | NZDIGIT't => Shift_act Nis'9 (eq_refl _)
    | MORE't => Shift_act Nis'10 (eq_refl _)
    | MINUS't => Shift_act Nis'11 (eq_refl _)
    | LPAR't => Shift_act Nis'12 (eq_refl _)
    | LOWX't => Shift_act Nis'16 (eq_refl _)
    | LOWW't => Shift_act Nis'17 (eq_refl _)
    | LOWV't => Shift_act Nis'18 (eq_refl _)
    | LOWU't => Shift_act Nis'19 (eq_refl _)
    | LOWT't => Shift_act Nis'20 (eq_refl _)
    | LOWS't => Shift_act Nis'21 (eq_refl _)
    | LOWR't => Shift_act Nis'22 (eq_refl _)
    | LOWP't => Shift_act Nis'23 (eq_refl _)
    | LOWN't => Shift_act Nis'24 (eq_refl _)
    | LOWK't => Shift_act Nis'25 (eq_refl _)
    | LOWF't => Shift_act Nis'26 (eq_refl _)
    | LOWD't => Shift_act Nis'27 (eq_refl _)
    | LOWB't => Shift_act Nis'28 (eq_refl _)
    | LESS't => Shift_act Nis'29 (eq_refl _)
    | LBRACK't => Shift_act Nis'30 (eq_refl _)
    | LBRAC't => Shift_act Nis'31 (eq_refl _)
    | EXCL't => Shift_act Nis'32 (eq_refl _)
    | EQUAL't => Shift_act Nis'33 (eq_refl _)
    | DOT't => Shift_act Nis'34 (eq_refl _)
    | COMMA't => Shift_act Nis'35 (eq_refl _)
    | COLONS't => Shift_act Nis'36 (eq_refl _)
    | CHAR't => Shift_act Nis'37 (eq_refl _)
    | ALT't => Reduce_act Prod'alternative'2
    | _ => Fail_act
    end)
  | Ninit Nis'70 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | RPAR't => Shift_act Nis'71 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'71 => Default_reduce_act Prod'assertion'2
  | Ninit Nis'72 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | ZERO't => Shift_act Nis'1 (eq_refl _)
    | UPW't => Shift_act Nis'2 (eq_refl _)
    | UPS't => Shift_act Nis'3 (eq_refl _)
    | UPP't => Shift_act Nis'4 (eq_refl _)
    | UPD't => Shift_act Nis'5 (eq_refl _)
    | UPB't => Shift_act Nis'6 (eq_refl _)
    | RPAR't => Reduce_act Prod'alternative'2
    | RBRACK't => Shift_act Nis'7 (eq_refl _)
    | RBRAC't => Shift_act Nis'8 (eq_refl _)
    | NZDIGIT't => Shift_act Nis'9 (eq_refl _)
    | MORE't => Shift_act Nis'10 (eq_refl _)
    | MINUS't => Shift_act Nis'11 (eq_refl _)
    | LPAR't => Shift_act Nis'12 (eq_refl _)
    | LOWX't => Shift_act Nis'16 (eq_refl _)
    | LOWW't => Shift_act Nis'17 (eq_refl _)
    | LOWV't => Shift_act Nis'18 (eq_refl _)
    | LOWU't => Shift_act Nis'19 (eq_refl _)
    | LOWT't => Shift_act Nis'20 (eq_refl _)
    | LOWS't => Shift_act Nis'21 (eq_refl _)
    | LOWR't => Shift_act Nis'22 (eq_refl _)
    | LOWP't => Shift_act Nis'23 (eq_refl _)
    | LOWN't => Shift_act Nis'24 (eq_refl _)
    | LOWK't => Shift_act Nis'25 (eq_refl _)
    | LOWF't => Shift_act Nis'26 (eq_refl _)
    | LOWD't => Shift_act Nis'27 (eq_refl _)
    | LOWB't => Shift_act Nis'28 (eq_refl _)
    | LESS't => Shift_act Nis'29 (eq_refl _)
    | LBRACK't => Shift_act Nis'30 (eq_refl _)
    | LBRAC't => Shift_act Nis'31 (eq_refl _)
    | EXCL't => Shift_act Nis'32 (eq_refl _)
    | EQUAL't => Shift_act Nis'33 (eq_refl _)
    | DOT't => Shift_act Nis'34 (eq_refl _)
    | COMMA't => Shift_act Nis'35 (eq_refl _)
    | COLONS't => Shift_act Nis'36 (eq_refl _)
    | CHAR't => Shift_act Nis'37 (eq_refl _)
    | ALT't => Reduce_act Prod'alternative'2
    | _ => Fail_act
    end)
  | Ninit Nis'73 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | RPAR't => Shift_act Nis'74 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'74 => Default_reduce_act Prod'assertion'1
  | Ninit Nis'75 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | ZERO't => Shift_act Nis'1 (eq_refl _)
    | UPW't => Shift_act Nis'2 (eq_refl _)
    | UPS't => Shift_act Nis'3 (eq_refl _)
    | UPP't => Shift_act Nis'4 (eq_refl _)
    | UPD't => Shift_act Nis'5 (eq_refl _)
    | UPB't => Shift_act Nis'6 (eq_refl _)
    | RPAR't => Reduce_act Prod'alternative'2
    | RBRACK't => Shift_act Nis'7 (eq_refl _)
    | RBRAC't => Shift_act Nis'8 (eq_refl _)
    | NZDIGIT't => Shift_act Nis'9 (eq_refl _)
    | MORE't => Shift_act Nis'10 (eq_refl _)
    | MINUS't => Shift_act Nis'11 (eq_refl _)
    | LPAR't => Shift_act Nis'12 (eq_refl _)
    | LOWX't => Shift_act Nis'16 (eq_refl _)
    | LOWW't => Shift_act Nis'17 (eq_refl _)
    | LOWV't => Shift_act Nis'18 (eq_refl _)
    | LOWU't => Shift_act Nis'19 (eq_refl _)
    | LOWT't => Shift_act Nis'20 (eq_refl _)
    | LOWS't => Shift_act Nis'21 (eq_refl _)
    | LOWR't => Shift_act Nis'22 (eq_refl _)
    | LOWP't => Shift_act Nis'23 (eq_refl _)
    | LOWN't => Shift_act Nis'24 (eq_refl _)
    | LOWK't => Shift_act Nis'25 (eq_refl _)
    | LOWF't => Shift_act Nis'26 (eq_refl _)
    | LOWD't => Shift_act Nis'27 (eq_refl _)
    | LOWB't => Shift_act Nis'28 (eq_refl _)
    | LESS't => Shift_act Nis'29 (eq_refl _)
    | LBRACK't => Shift_act Nis'30 (eq_refl _)
    | LBRAC't => Shift_act Nis'31 (eq_refl _)
    | EXCL't => Shift_act Nis'32 (eq_refl _)
    | EQUAL't => Shift_act Nis'33 (eq_refl _)
    | DOT't => Shift_act Nis'34 (eq_refl _)
    | COMMA't => Shift_act Nis'35 (eq_refl _)
    | COLONS't => Shift_act Nis'36 (eq_refl _)
    | CHAR't => Shift_act Nis'37 (eq_refl _)
    | ALT't => Reduce_act Prod'alternative'2
    | _ => Fail_act
    end)
  | Ninit Nis'76 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | RPAR't => Shift_act Nis'77 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'77 => Default_reduce_act Prod'assertion'0
  | Ninit Nis'78 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | EOF't => Shift_act Nis'79 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'79 => Default_reduce_act Prod'main'0
  | Ninit Nis'81 => Default_reduce_act Prod'pattern'0
  end.

Definition goto_table (state:state) (nt:nonterminal) :=
  match state, nt return option { s:noninitstate | NT nt = last_symb_of_non_init_state s } with
  | Init Init'0, term'nt => Some (exist _ Nis'38 (eq_refl _))
  | Init Init'0, patterncharacter'nt => Some (exist _ Nis'39 (eq_refl _))
  | Init Init'0, pattern'nt => Some (exist _ Nis'78 (eq_refl _))
  | Init Init'0, main'nt => None  | Init Init'0, disjunction'nt => Some (exist _ Nis'81 (eq_refl _))
  | Init Init'0, decimaldigit'nt => Some (exist _ Nis'42 (eq_refl _))
  | Init Init'0, atom'nt => Some (exist _ Nis'43 (eq_refl _))
  | Init Init'0, assertion'nt => Some (exist _ Nis'64 (eq_refl _))
  | Init Init'0, alternative'nt => Some (exist _ Nis'65 (eq_refl _))
  | Ninit Nis'15, term'nt => Some (exist _ Nis'38 (eq_refl _))
  | Ninit Nis'15, patterncharacter'nt => Some (exist _ Nis'39 (eq_refl _))
  | Ninit Nis'15, disjunction'nt => Some (exist _ Nis'40 (eq_refl _))
  | Ninit Nis'15, decimaldigit'nt => Some (exist _ Nis'42 (eq_refl _))
  | Ninit Nis'15, atom'nt => Some (exist _ Nis'43 (eq_refl _))
  | Ninit Nis'15, assertion'nt => Some (exist _ Nis'64 (eq_refl _))
  | Ninit Nis'15, alternative'nt => Some (exist _ Nis'65 (eq_refl _))
  | Ninit Nis'43, quantifier'nt => Some (exist _ Nis'63 (eq_refl _))
  | Ninit Nis'50, decimaldigits_'nt => Some (exist _ Nis'51 (eq_refl _))
  | Ninit Nis'50, decimaldigits'nt => Some (exist _ Nis'53 (eq_refl _))
  | Ninit Nis'50, decimaldigit'nt => Some (exist _ Nis'62 (eq_refl _))
  | Ninit Nis'51, decimaldigit'nt => Some (exist _ Nis'52 (eq_refl _))
  | Ninit Nis'56, decimaldigits_'nt => Some (exist _ Nis'51 (eq_refl _))
  | Ninit Nis'56, decimaldigits'nt => Some (exist _ Nis'59 (eq_refl _))
  | Ninit Nis'56, decimaldigit'nt => Some (exist _ Nis'62 (eq_refl _))
  | Ninit Nis'65, term'nt => Some (exist _ Nis'68 (eq_refl _))
  | Ninit Nis'65, patterncharacter'nt => Some (exist _ Nis'39 (eq_refl _))
  | Ninit Nis'65, decimaldigit'nt => Some (exist _ Nis'42 (eq_refl _))
  | Ninit Nis'65, atom'nt => Some (exist _ Nis'43 (eq_refl _))
  | Ninit Nis'65, assertion'nt => Some (exist _ Nis'64 (eq_refl _))
  | Ninit Nis'66, term'nt => Some (exist _ Nis'38 (eq_refl _))
  | Ninit Nis'66, patterncharacter'nt => Some (exist _ Nis'39 (eq_refl _))
  | Ninit Nis'66, disjunction'nt => Some (exist _ Nis'67 (eq_refl _))
  | Ninit Nis'66, decimaldigit'nt => Some (exist _ Nis'42 (eq_refl _))
  | Ninit Nis'66, atom'nt => Some (exist _ Nis'43 (eq_refl _))
  | Ninit Nis'66, assertion'nt => Some (exist _ Nis'64 (eq_refl _))
  | Ninit Nis'66, alternative'nt => Some (exist _ Nis'65 (eq_refl _))
  | Ninit Nis'69, term'nt => Some (exist _ Nis'38 (eq_refl _))
  | Ninit Nis'69, patterncharacter'nt => Some (exist _ Nis'39 (eq_refl _))
  | Ninit Nis'69, disjunction'nt => Some (exist _ Nis'70 (eq_refl _))
  | Ninit Nis'69, decimaldigit'nt => Some (exist _ Nis'42 (eq_refl _))
  | Ninit Nis'69, atom'nt => Some (exist _ Nis'43 (eq_refl _))
  | Ninit Nis'69, assertion'nt => Some (exist _ Nis'64 (eq_refl _))
  | Ninit Nis'69, alternative'nt => Some (exist _ Nis'65 (eq_refl _))
  | Ninit Nis'72, term'nt => Some (exist _ Nis'38 (eq_refl _))
  | Ninit Nis'72, patterncharacter'nt => Some (exist _ Nis'39 (eq_refl _))
  | Ninit Nis'72, disjunction'nt => Some (exist _ Nis'73 (eq_refl _))
  | Ninit Nis'72, decimaldigit'nt => Some (exist _ Nis'42 (eq_refl _))
  | Ninit Nis'72, atom'nt => Some (exist _ Nis'43 (eq_refl _))
  | Ninit Nis'72, assertion'nt => Some (exist _ Nis'64 (eq_refl _))
  | Ninit Nis'72, alternative'nt => Some (exist _ Nis'65 (eq_refl _))
  | Ninit Nis'75, term'nt => Some (exist _ Nis'38 (eq_refl _))
  | Ninit Nis'75, patterncharacter'nt => Some (exist _ Nis'39 (eq_refl _))
  | Ninit Nis'75, disjunction'nt => Some (exist _ Nis'76 (eq_refl _))
  | Ninit Nis'75, decimaldigit'nt => Some (exist _ Nis'42 (eq_refl _))
  | Ninit Nis'75, atom'nt => Some (exist _ Nis'43 (eq_refl _))
  | Ninit Nis'75, assertion'nt => Some (exist _ Nis'64 (eq_refl _))
  | Ninit Nis'75, alternative'nt => Some (exist _ Nis'65 (eq_refl _))
  | _, _ => None
  end.

Definition past_symb_of_non_init_state (noninitstate:noninitstate) : list symbol :=
  match noninitstate with
  | Nis'1 => []%list
  | Nis'2 => []%list
  | Nis'3 => []%list
  | Nis'4 => []%list
  | Nis'5 => []%list
  | Nis'6 => []%list
  | Nis'7 => []%list
  | Nis'8 => []%list
  | Nis'9 => []%list
  | Nis'10 => []%list
  | Nis'11 => []%list
  | Nis'12 => []%list
  | Nis'13 => [T LPAR't]%list
  | Nis'14 => [T QMARK't; T LPAR't]%list
  | Nis'15 => [T LESS't; T QMARK't; T LPAR't]%list
  | Nis'16 => []%list
  | Nis'17 => []%list
  | Nis'18 => []%list
  | Nis'19 => []%list
  | Nis'20 => []%list
  | Nis'21 => []%list
  | Nis'22 => []%list
  | Nis'23 => []%list
  | Nis'24 => []%list
  | Nis'25 => []%list
  | Nis'26 => []%list
  | Nis'27 => []%list
  | Nis'28 => []%list
  | Nis'29 => []%list
  | Nis'30 => []%list
  | Nis'31 => []%list
  | Nis'32 => []%list
  | Nis'33 => []%list
  | Nis'34 => []%list
  | Nis'35 => []%list
  | Nis'36 => []%list
  | Nis'37 => []%list
  | Nis'38 => []%list
  | Nis'39 => []%list
  | Nis'40 => [T EXCL't; T LESS't; T QMARK't; T LPAR't]%list
  | Nis'41 => [NT disjunction'nt; T EXCL't; T LESS't; T QMARK't; T LPAR't]%list
  | Nis'42 => []%list
  | Nis'43 => []%list
  | Nis'44 => []%list
  | Nis'45 => [T STAR't]%list
  | Nis'46 => []%list
  | Nis'47 => [T QMARK't]%list
  | Nis'48 => []%list
  | Nis'49 => [T PLUS't]%list
  | Nis'50 => []%list
  | Nis'51 => []%list
  | Nis'52 => [NT decimaldigits_'nt]%list
  | Nis'53 => [T LBRAC't]%list
  | Nis'54 => [NT decimaldigits'nt; T LBRAC't]%list
  | Nis'55 => [T RBRAC't; NT decimaldigits'nt; T LBRAC't]%list
  | Nis'56 => [NT decimaldigits'nt; T LBRAC't]%list
  | Nis'57 => [T COMMA't; NT decimaldigits'nt; T LBRAC't]%list
  | Nis'58 => [T RBRAC't; T COMMA't; NT decimaldigits'nt; T LBRAC't]%list
  | Nis'59 => [T COMMA't; NT decimaldigits'nt; T LBRAC't]%list
  | Nis'60 => [NT decimaldigits'nt; T COMMA't; NT decimaldigits'nt; T LBRAC't]%list
  | Nis'61 => [T RBRAC't; NT decimaldigits'nt; T COMMA't; NT decimaldigits'nt; T LBRAC't]%list
  | Nis'62 => []%list
  | Nis'63 => [NT atom'nt]%list
  | Nis'64 => []%list
  | Nis'65 => []%list
  | Nis'66 => [NT alternative'nt]%list
  | Nis'67 => [T ALT't; NT alternative'nt]%list
  | Nis'68 => [NT alternative'nt]%list
  | Nis'69 => [T LESS't; T QMARK't; T LPAR't]%list
  | Nis'70 => [T EQUAL't; T LESS't; T QMARK't; T LPAR't]%list
  | Nis'71 => [NT disjunction'nt; T EQUAL't; T LESS't; T QMARK't; T LPAR't]%list
  | Nis'72 => [T QMARK't; T LPAR't]%list
  | Nis'73 => [T EXCL't; T QMARK't; T LPAR't]%list
  | Nis'74 => [NT disjunction'nt; T EXCL't; T QMARK't; T LPAR't]%list
  | Nis'75 => [T QMARK't; T LPAR't]%list
  | Nis'76 => [T EQUAL't; T QMARK't; T LPAR't]%list
  | Nis'77 => [NT disjunction'nt; T EQUAL't; T QMARK't; T LPAR't]%list
  | Nis'78 => []%list
  | Nis'79 => [NT pattern'nt]%list
  | Nis'81 => []%list
  end.
Extract Constant past_symb_of_non_init_state => "fun _ -> assert false".

Definition state_set_1 (s:state) : bool :=
  match s with
  | Init Init'0 | Ninit Nis'15 | Ninit Nis'50 | Ninit Nis'51 | Ninit Nis'56 | Ninit Nis'65 | Ninit Nis'66 | Ninit Nis'69 | Ninit Nis'72 | Ninit Nis'75 => true
  | _ => false
  end.
Extract Inlined Constant state_set_1 => "assert false".

Definition state_set_2 (s:state) : bool :=
  match s with
  | Init Init'0 | Ninit Nis'15 | Ninit Nis'65 | Ninit Nis'66 | Ninit Nis'69 | Ninit Nis'72 | Ninit Nis'75 => true
  | _ => false
  end.
Extract Inlined Constant state_set_2 => "assert false".

Definition state_set_3 (s:state) : bool :=
  match s with
  | Ninit Nis'12 => true
  | _ => false
  end.
Extract Inlined Constant state_set_3 => "assert false".

Definition state_set_4 (s:state) : bool :=
  match s with
  | Ninit Nis'13 => true
  | _ => false
  end.
Extract Inlined Constant state_set_4 => "assert false".

Definition state_set_5 (s:state) : bool :=
  match s with
  | Ninit Nis'14 => true
  | _ => false
  end.
Extract Inlined Constant state_set_5 => "assert false".

Definition state_set_6 (s:state) : bool :=
  match s with
  | Init Init'0 | Ninit Nis'15 | Ninit Nis'66 | Ninit Nis'69 | Ninit Nis'72 | Ninit Nis'75 => true
  | _ => false
  end.
Extract Inlined Constant state_set_6 => "assert false".

Definition state_set_7 (s:state) : bool :=
  match s with
  | Ninit Nis'15 => true
  | _ => false
  end.
Extract Inlined Constant state_set_7 => "assert false".

Definition state_set_8 (s:state) : bool :=
  match s with
  | Ninit Nis'40 => true
  | _ => false
  end.
Extract Inlined Constant state_set_8 => "assert false".

Definition state_set_9 (s:state) : bool :=
  match s with
  | Ninit Nis'43 => true
  | _ => false
  end.
Extract Inlined Constant state_set_9 => "assert false".

Definition state_set_10 (s:state) : bool :=
  match s with
  | Ninit Nis'44 => true
  | _ => false
  end.
Extract Inlined Constant state_set_10 => "assert false".

Definition state_set_11 (s:state) : bool :=
  match s with
  | Ninit Nis'46 => true
  | _ => false
  end.
Extract Inlined Constant state_set_11 => "assert false".

Definition state_set_12 (s:state) : bool :=
  match s with
  | Ninit Nis'48 => true
  | _ => false
  end.
Extract Inlined Constant state_set_12 => "assert false".

Definition state_set_13 (s:state) : bool :=
  match s with
  | Ninit Nis'50 | Ninit Nis'56 => true
  | _ => false
  end.
Extract Inlined Constant state_set_13 => "assert false".

Definition state_set_14 (s:state) : bool :=
  match s with
  | Ninit Nis'51 => true
  | _ => false
  end.
Extract Inlined Constant state_set_14 => "assert false".

Definition state_set_15 (s:state) : bool :=
  match s with
  | Ninit Nis'50 => true
  | _ => false
  end.
Extract Inlined Constant state_set_15 => "assert false".

Definition state_set_16 (s:state) : bool :=
  match s with
  | Ninit Nis'53 => true
  | _ => false
  end.
Extract Inlined Constant state_set_16 => "assert false".

Definition state_set_17 (s:state) : bool :=
  match s with
  | Ninit Nis'54 => true
  | _ => false
  end.
Extract Inlined Constant state_set_17 => "assert false".

Definition state_set_18 (s:state) : bool :=
  match s with
  | Ninit Nis'56 => true
  | _ => false
  end.
Extract Inlined Constant state_set_18 => "assert false".

Definition state_set_19 (s:state) : bool :=
  match s with
  | Ninit Nis'57 => true
  | _ => false
  end.
Extract Inlined Constant state_set_19 => "assert false".

Definition state_set_20 (s:state) : bool :=
  match s with
  | Ninit Nis'59 => true
  | _ => false
  end.
Extract Inlined Constant state_set_20 => "assert false".

Definition state_set_21 (s:state) : bool :=
  match s with
  | Ninit Nis'60 => true
  | _ => false
  end.
Extract Inlined Constant state_set_21 => "assert false".

Definition state_set_22 (s:state) : bool :=
  match s with
  | Ninit Nis'65 => true
  | _ => false
  end.
Extract Inlined Constant state_set_22 => "assert false".

Definition state_set_23 (s:state) : bool :=
  match s with
  | Ninit Nis'66 => true
  | _ => false
  end.
Extract Inlined Constant state_set_23 => "assert false".

Definition state_set_24 (s:state) : bool :=
  match s with
  | Ninit Nis'69 => true
  | _ => false
  end.
Extract Inlined Constant state_set_24 => "assert false".

Definition state_set_25 (s:state) : bool :=
  match s with
  | Ninit Nis'70 => true
  | _ => false
  end.
Extract Inlined Constant state_set_25 => "assert false".

Definition state_set_26 (s:state) : bool :=
  match s with
  | Ninit Nis'72 => true
  | _ => false
  end.
Extract Inlined Constant state_set_26 => "assert false".

Definition state_set_27 (s:state) : bool :=
  match s with
  | Ninit Nis'73 => true
  | _ => false
  end.
Extract Inlined Constant state_set_27 => "assert false".

Definition state_set_28 (s:state) : bool :=
  match s with
  | Ninit Nis'75 => true
  | _ => false
  end.
Extract Inlined Constant state_set_28 => "assert false".

Definition state_set_29 (s:state) : bool :=
  match s with
  | Ninit Nis'76 => true
  | _ => false
  end.
Extract Inlined Constant state_set_29 => "assert false".

Definition state_set_30 (s:state) : bool :=
  match s with
  | Init Init'0 => true
  | _ => false
  end.
Extract Inlined Constant state_set_30 => "assert false".

Definition state_set_31 (s:state) : bool :=
  match s with
  | Ninit Nis'78 => true
  | _ => false
  end.
Extract Inlined Constant state_set_31 => "assert false".

Definition past_state_of_non_init_state (s:noninitstate) : list (state -> bool) :=
  match s with
  | Nis'1 => [state_set_1]%list
  | Nis'2 => [state_set_2]%list
  | Nis'3 => [state_set_2]%list
  | Nis'4 => [state_set_2]%list
  | Nis'5 => [state_set_2]%list
  | Nis'6 => [state_set_2]%list
  | Nis'7 => [state_set_2]%list
  | Nis'8 => [state_set_2]%list
  | Nis'9 => [state_set_1]%list
  | Nis'10 => [state_set_2]%list
  | Nis'11 => [state_set_2]%list
  | Nis'12 => [state_set_2]%list
  | Nis'13 => [state_set_3; state_set_2]%list
  | Nis'14 => [state_set_4; state_set_3; state_set_2]%list
  | Nis'15 => [state_set_5; state_set_4; state_set_3; state_set_2]%list
  | Nis'16 => [state_set_2]%list
  | Nis'17 => [state_set_2]%list
  | Nis'18 => [state_set_2]%list
  | Nis'19 => [state_set_2]%list
  | Nis'20 => [state_set_2]%list
  | Nis'21 => [state_set_2]%list
  | Nis'22 => [state_set_2]%list
  | Nis'23 => [state_set_2]%list
  | Nis'24 => [state_set_2]%list
  | Nis'25 => [state_set_2]%list
  | Nis'26 => [state_set_2]%list
  | Nis'27 => [state_set_2]%list
  | Nis'28 => [state_set_2]%list
  | Nis'29 => [state_set_2]%list
  | Nis'30 => [state_set_2]%list
  | Nis'31 => [state_set_2]%list
  | Nis'32 => [state_set_2]%list
  | Nis'33 => [state_set_2]%list
  | Nis'34 => [state_set_2]%list
  | Nis'35 => [state_set_2]%list
  | Nis'36 => [state_set_2]%list
  | Nis'37 => [state_set_2]%list
  | Nis'38 => [state_set_6]%list
  | Nis'39 => [state_set_2]%list
  | Nis'40 => [state_set_7; state_set_5; state_set_4; state_set_3; state_set_2]%list
  | Nis'41 => [state_set_8; state_set_7; state_set_5; state_set_4; state_set_3; state_set_2]%list
  | Nis'42 => [state_set_2]%list
  | Nis'43 => [state_set_2]%list
  | Nis'44 => [state_set_9]%list
  | Nis'45 => [state_set_10; state_set_9]%list
  | Nis'46 => [state_set_9]%list
  | Nis'47 => [state_set_11; state_set_9]%list
  | Nis'48 => [state_set_9]%list
  | Nis'49 => [state_set_12; state_set_9]%list
  | Nis'50 => [state_set_9]%list
  | Nis'51 => [state_set_13]%list
  | Nis'52 => [state_set_14; state_set_13]%list
  | Nis'53 => [state_set_15; state_set_9]%list
  | Nis'54 => [state_set_16; state_set_15; state_set_9]%list
  | Nis'55 => [state_set_17; state_set_16; state_set_15; state_set_9]%list
  | Nis'56 => [state_set_16; state_set_15; state_set_9]%list
  | Nis'57 => [state_set_18; state_set_16; state_set_15; state_set_9]%list
  | Nis'58 => [state_set_19; state_set_18; state_set_16; state_set_15; state_set_9]%list
  | Nis'59 => [state_set_18; state_set_16; state_set_15; state_set_9]%list
  | Nis'60 => [state_set_20; state_set_18; state_set_16; state_set_15; state_set_9]%list
  | Nis'61 => [state_set_21; state_set_20; state_set_18; state_set_16; state_set_15; state_set_9]%list
  | Nis'62 => [state_set_13]%list
  | Nis'63 => [state_set_9; state_set_2]%list
  | Nis'64 => [state_set_2]%list
  | Nis'65 => [state_set_6]%list
  | Nis'66 => [state_set_22; state_set_6]%list
  | Nis'67 => [state_set_23; state_set_22; state_set_6]%list
  | Nis'68 => [state_set_22; state_set_6]%list
  | Nis'69 => [state_set_5; state_set_4; state_set_3; state_set_2]%list
  | Nis'70 => [state_set_24; state_set_5; state_set_4; state_set_3; state_set_2]%list
  | Nis'71 => [state_set_25; state_set_24; state_set_5; state_set_4; state_set_3; state_set_2]%list
  | Nis'72 => [state_set_4; state_set_3; state_set_2]%list
  | Nis'73 => [state_set_26; state_set_4; state_set_3; state_set_2]%list
  | Nis'74 => [state_set_27; state_set_26; state_set_4; state_set_3; state_set_2]%list
  | Nis'75 => [state_set_4; state_set_3; state_set_2]%list
  | Nis'76 => [state_set_28; state_set_4; state_set_3; state_set_2]%list
  | Nis'77 => [state_set_29; state_set_28; state_set_4; state_set_3; state_set_2]%list
  | Nis'78 => [state_set_30]%list
  | Nis'79 => [state_set_31; state_set_30]%list
  | Nis'81 => [state_set_30]%list
  end.
Extract Constant past_state_of_non_init_state => "fun _ -> assert false".

Definition lookahead_set_1 : list terminal :=
  [ZERO't; UPW't; UPS't; UPP't; UPD't; UPB't; RBRACK't; RBRAC't; NZDIGIT't; MORE't; MINUS't; LPAR't; LOWX't; LOWW't; LOWV't; LOWU't; LOWT't; LOWS't; LOWR't; LOWP't; LOWN't; LOWK't; LOWF't; LOWD't; LOWB't; LESS't; LBRACK't; LBRAC't; EXCL't; EQUAL't; EOF't; DOT't; COMMA't; COLONS't; CHAR't; ALT't]%list.
Extract Inlined Constant lookahead_set_1 => "assert false".

Definition lookahead_set_2 : list terminal :=
  [ZERO't; UPW't; UPS't; UPP't; UPD't; UPB't; STAR't; RBRACK't; RBRAC't; QMARK't; PLUS't; NZDIGIT't; MORE't; MINUS't; LPAR't; LOWX't; LOWW't; LOWV't; LOWU't; LOWT't; LOWS't; LOWR't; LOWP't; LOWN't; LOWK't; LOWF't; LOWD't; LOWB't; LESS't; LBRACK't; LBRAC't; EXCL't; EQUAL't; EOF't; DOT't; COMMA't; COLONS't; CHAR't; ALT't]%list.
Extract Inlined Constant lookahead_set_2 => "assert false".

Definition lookahead_set_3 : list terminal :=
  [EOF't]%list.
Extract Inlined Constant lookahead_set_3 => "assert false".

Definition lookahead_set_4 : list terminal :=
  [ZERO't; UPW't; UPS't; UPP't; UPD't; UPB't; STAR't; RPAR't; RBRACK't; RBRAC't; QMARK't; PLUS't; NZDIGIT't; MORE't; MINUS't; LPAR't; LOWX't; LOWW't; LOWV't; LOWU't; LOWT't; LOWS't; LOWR't; LOWP't; LOWN't; LOWK't; LOWF't; LOWD't; LOWB't; LESS't; LBRACK't; LBRAC't; HAT't; EXCL't; EQUAL't; EOF't; DOT't; DOLLAR't; COMMA't; COLONS't; CHAR't; BACKSL't; ALT't]%list.
Extract Inlined Constant lookahead_set_4 => "assert false".

Definition lookahead_set_5 : list terminal :=
  [ZERO't; UPW't; UPS't; UPP't; UPD't; UPB't; STAR't; RPAR't; RBRACK't; RBRAC't; QMARK't; PLUS't; NZDIGIT't; MORE't; MINUS't; LPAR't; LOWX't; LOWW't; LOWV't; LOWU't; LOWT't; LOWS't; LOWR't; LOWP't; LOWN't; LOWK't; LOWF't; LOWD't; LOWB't; LESS't; LBRACK't; LBRAC't; EXCL't; EQUAL't; EOF't; DOT't; COMMA't; COLONS't; CHAR't; ALT't]%list.
Extract Inlined Constant lookahead_set_5 => "assert false".

Definition lookahead_set_6 : list terminal :=
  [ZERO't; UPW't; UPS't; UPP't; UPD't; UPB't; RPAR't; RBRACK't; RBRAC't; NZDIGIT't; MORE't; MINUS't; LPAR't; LOWX't; LOWW't; LOWV't; LOWU't; LOWT't; LOWS't; LOWR't; LOWP't; LOWN't; LOWK't; LOWF't; LOWD't; LOWB't; LESS't; LBRACK't; LBRAC't; EXCL't; EQUAL't; EOF't; DOT't; COMMA't; COLONS't; CHAR't; ALT't]%list.
Extract Inlined Constant lookahead_set_6 => "assert false".

Definition lookahead_set_7 : list terminal :=
  [ZERO't; UPW't; UPS't; UPP't; UPD't; UPB't; RPAR't; RBRACK't; RBRAC't; NZDIGIT't; MORE't; MINUS't; LPAR't; LOWX't; LOWW't; LOWV't; LOWU't; LOWT't; LOWS't; LOWR't; LOWP't; LOWN't; LOWK't; LOWF't; LOWD't; LOWB't; LESS't; LBRACK't; LBRAC't; EXCL't; EQUAL't; DOT't; COMMA't; COLONS't; CHAR't; ALT't]%list.
Extract Inlined Constant lookahead_set_7 => "assert false".

Definition lookahead_set_8 : list terminal :=
  [ZERO't; UPW't; UPS't; UPP't; UPD't; UPB't; STAR't; RPAR't; RBRACK't; RBRAC't; QMARK't; PLUS't; NZDIGIT't; MORE't; MINUS't; LPAR't; LOWX't; LOWW't; LOWV't; LOWU't; LOWT't; LOWS't; LOWR't; LOWP't; LOWN't; LOWK't; LOWF't; LOWD't; LOWB't; LESS't; LBRACK't; LBRAC't; EXCL't; EQUAL't; DOT't; COMMA't; COLONS't; CHAR't; ALT't]%list.
Extract Inlined Constant lookahead_set_8 => "assert false".

Definition lookahead_set_9 : list terminal :=
  [RPAR't]%list.
Extract Inlined Constant lookahead_set_9 => "assert false".

Definition lookahead_set_10 : list terminal :=
  [ZERO't; RBRAC't; NZDIGIT't; COMMA't]%list.
Extract Inlined Constant lookahead_set_10 => "assert false".

Definition lookahead_set_11 : list terminal :=
  [RBRAC't; COMMA't]%list.
Extract Inlined Constant lookahead_set_11 => "assert false".

Definition lookahead_set_12 : list terminal :=
  [ZERO't; RBRAC't; NZDIGIT't]%list.
Extract Inlined Constant lookahead_set_12 => "assert false".

Definition lookahead_set_13 : list terminal :=
  [RBRAC't]%list.
Extract Inlined Constant lookahead_set_13 => "assert false".

Definition lookahead_set_14 : list terminal :=
  [RPAR't; EOF't]%list.
Extract Inlined Constant lookahead_set_14 => "assert false".

Definition items_of_state_0 : list item :=
  [ {| prod_item := Prod'alternative'0; dot_pos_item := 0; lookaheads_item := lookahead_set_1 |};
    {| prod_item := Prod'alternative'1; dot_pos_item := 0; lookaheads_item := lookahead_set_1 |};
    {| prod_item := Prod'alternative'2; dot_pos_item := 0; lookaheads_item := lookahead_set_1 |};
    {| prod_item := Prod'assertion'0; dot_pos_item := 0; lookaheads_item := lookahead_set_1 |};
    {| prod_item := Prod'assertion'1; dot_pos_item := 0; lookaheads_item := lookahead_set_1 |};
    {| prod_item := Prod'assertion'2; dot_pos_item := 0; lookaheads_item := lookahead_set_1 |};
    {| prod_item := Prod'assertion'3; dot_pos_item := 0; lookaheads_item := lookahead_set_1 |};
    {| prod_item := Prod'atom'0; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'atom'1; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'decimaldigit'0; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'decimaldigit'1; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'disjunction'0; dot_pos_item := 0; lookaheads_item := lookahead_set_3 |};
    {| prod_item := Prod'disjunction'1; dot_pos_item := 0; lookaheads_item := lookahead_set_3 |};
    {| prod_item := Prod'main'0; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'pattern'0; dot_pos_item := 0; lookaheads_item := lookahead_set_3 |};
    {| prod_item := Prod'patterncharacter'0; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'patterncharacter'1; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'patterncharacter'2; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'patterncharacter'3; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'patterncharacter'4; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'patterncharacter'5; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'patterncharacter'6; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'patterncharacter'7; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'patterncharacter'8; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'patterncharacter'9; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'patterncharacter'10; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'patterncharacter'11; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'patterncharacter'12; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'patterncharacter'13; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'patterncharacter'14; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'patterncharacter'15; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'patterncharacter'16; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'patterncharacter'17; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'patterncharacter'18; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'patterncharacter'19; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'patterncharacter'20; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'patterncharacter'21; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'patterncharacter'22; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'patterncharacter'23; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'patterncharacter'24; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'patterncharacter'25; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'patterncharacter'26; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'patterncharacter'27; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'patterncharacter'28; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'patterncharacter'29; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'patterncharacter'30; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'term'0; dot_pos_item := 0; lookaheads_item := lookahead_set_1 |};
    {| prod_item := Prod'term'1; dot_pos_item := 0; lookaheads_item := lookahead_set_1 |};
    {| prod_item := Prod'term'2; dot_pos_item := 0; lookaheads_item := lookahead_set_1 |} ]%list.
Extract Inlined Constant items_of_state_0 => "assert false".

Definition items_of_state_1 : list item :=
  [ {| prod_item := Prod'decimaldigit'1; dot_pos_item := 1; lookaheads_item := lookahead_set_5 |} ]%list.
Extract Inlined Constant items_of_state_1 => "assert false".

Definition items_of_state_2 : list item :=
  [ {| prod_item := Prod'patterncharacter'8; dot_pos_item := 1; lookaheads_item := lookahead_set_5 |} ]%list.
Extract Inlined Constant items_of_state_2 => "assert false".

Definition items_of_state_3 : list item :=
  [ {| prod_item := Prod'patterncharacter'6; dot_pos_item := 1; lookaheads_item := lookahead_set_5 |} ]%list.
Extract Inlined Constant items_of_state_3 => "assert false".

Definition items_of_state_4 : list item :=
  [ {| prod_item := Prod'patterncharacter'18; dot_pos_item := 1; lookaheads_item := lookahead_set_5 |} ]%list.
Extract Inlined Constant items_of_state_4 => "assert false".

Definition items_of_state_5 : list item :=
  [ {| prod_item := Prod'patterncharacter'4; dot_pos_item := 1; lookaheads_item := lookahead_set_5 |} ]%list.
Extract Inlined Constant items_of_state_5 => "assert false".

Definition items_of_state_6 : list item :=
  [ {| prod_item := Prod'patterncharacter'2; dot_pos_item := 1; lookaheads_item := lookahead_set_5 |} ]%list.
Extract Inlined Constant items_of_state_6 => "assert false".

Definition items_of_state_7 : list item :=
  [ {| prod_item := Prod'patterncharacter'29; dot_pos_item := 1; lookaheads_item := lookahead_set_5 |} ]%list.
Extract Inlined Constant items_of_state_7 => "assert false".

Definition items_of_state_8 : list item :=
  [ {| prod_item := Prod'patterncharacter'27; dot_pos_item := 1; lookaheads_item := lookahead_set_5 |} ]%list.
Extract Inlined Constant items_of_state_8 => "assert false".

Definition items_of_state_9 : list item :=
  [ {| prod_item := Prod'decimaldigit'0; dot_pos_item := 1; lookaheads_item := lookahead_set_5 |} ]%list.
Extract Inlined Constant items_of_state_9 => "assert false".

Definition items_of_state_10 : list item :=
  [ {| prod_item := Prod'patterncharacter'22; dot_pos_item := 1; lookaheads_item := lookahead_set_5 |} ]%list.
Extract Inlined Constant items_of_state_10 => "assert false".

Definition items_of_state_11 : list item :=
  [ {| prod_item := Prod'patterncharacter'24; dot_pos_item := 1; lookaheads_item := lookahead_set_5 |} ]%list.
Extract Inlined Constant items_of_state_11 => "assert false".

Definition items_of_state_12 : list item :=
  [ {| prod_item := Prod'assertion'0; dot_pos_item := 1; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'assertion'1; dot_pos_item := 1; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'assertion'2; dot_pos_item := 1; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'assertion'3; dot_pos_item := 1; lookaheads_item := lookahead_set_6 |} ]%list.
Extract Inlined Constant items_of_state_12 => "assert false".

Definition items_of_state_13 : list item :=
  [ {| prod_item := Prod'assertion'0; dot_pos_item := 2; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'assertion'1; dot_pos_item := 2; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'assertion'2; dot_pos_item := 2; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'assertion'3; dot_pos_item := 2; lookaheads_item := lookahead_set_6 |} ]%list.
Extract Inlined Constant items_of_state_13 => "assert false".

Definition items_of_state_14 : list item :=
  [ {| prod_item := Prod'assertion'2; dot_pos_item := 3; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'assertion'3; dot_pos_item := 3; lookaheads_item := lookahead_set_6 |} ]%list.
Extract Inlined Constant items_of_state_14 => "assert false".

Definition items_of_state_15 : list item :=
  [ {| prod_item := Prod'alternative'0; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |};
    {| prod_item := Prod'alternative'1; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |};
    {| prod_item := Prod'alternative'2; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |};
    {| prod_item := Prod'assertion'0; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |};
    {| prod_item := Prod'assertion'1; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |};
    {| prod_item := Prod'assertion'2; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |};
    {| prod_item := Prod'assertion'3; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |};
    {| prod_item := Prod'assertion'3; dot_pos_item := 4; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'atom'0; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'atom'1; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'decimaldigit'0; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'decimaldigit'1; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'disjunction'0; dot_pos_item := 0; lookaheads_item := lookahead_set_9 |};
    {| prod_item := Prod'disjunction'1; dot_pos_item := 0; lookaheads_item := lookahead_set_9 |};
    {| prod_item := Prod'patterncharacter'0; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'1; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'2; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'3; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'4; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'5; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'6; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'7; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'8; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'9; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'10; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'11; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'12; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'13; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'14; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'15; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'16; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'17; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'18; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'19; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'20; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'21; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'22; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'23; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'24; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'25; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'26; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'27; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'28; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'29; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'30; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'term'0; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |};
    {| prod_item := Prod'term'1; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |};
    {| prod_item := Prod'term'2; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |} ]%list.
Extract Inlined Constant items_of_state_15 => "assert false".

Definition items_of_state_16 : list item :=
  [ {| prod_item := Prod'patterncharacter'15; dot_pos_item := 1; lookaheads_item := lookahead_set_5 |} ]%list.
Extract Inlined Constant items_of_state_16 => "assert false".

Definition items_of_state_17 : list item :=
  [ {| prod_item := Prod'patterncharacter'7; dot_pos_item := 1; lookaheads_item := lookahead_set_5 |} ]%list.
Extract Inlined Constant items_of_state_17 => "assert false".

Definition items_of_state_18 : list item :=
  [ {| prod_item := Prod'patterncharacter'13; dot_pos_item := 1; lookaheads_item := lookahead_set_5 |} ]%list.
Extract Inlined Constant items_of_state_18 => "assert false".

Definition items_of_state_19 : list item :=
  [ {| prod_item := Prod'patterncharacter'16; dot_pos_item := 1; lookaheads_item := lookahead_set_5 |} ]%list.
Extract Inlined Constant items_of_state_19 => "assert false".

Definition items_of_state_20 : list item :=
  [ {| prod_item := Prod'patterncharacter'12; dot_pos_item := 1; lookaheads_item := lookahead_set_5 |} ]%list.
Extract Inlined Constant items_of_state_20 => "assert false".

Definition items_of_state_21 : list item :=
  [ {| prod_item := Prod'patterncharacter'5; dot_pos_item := 1; lookaheads_item := lookahead_set_5 |} ]%list.
Extract Inlined Constant items_of_state_21 => "assert false".

Definition items_of_state_22 : list item :=
  [ {| prod_item := Prod'patterncharacter'11; dot_pos_item := 1; lookaheads_item := lookahead_set_5 |} ]%list.
Extract Inlined Constant items_of_state_22 => "assert false".

Definition items_of_state_23 : list item :=
  [ {| prod_item := Prod'patterncharacter'17; dot_pos_item := 1; lookaheads_item := lookahead_set_5 |} ]%list.
Extract Inlined Constant items_of_state_23 => "assert false".

Definition items_of_state_24 : list item :=
  [ {| prod_item := Prod'patterncharacter'10; dot_pos_item := 1; lookaheads_item := lookahead_set_5 |} ]%list.
Extract Inlined Constant items_of_state_24 => "assert false".

Definition items_of_state_25 : list item :=
  [ {| prod_item := Prod'patterncharacter'14; dot_pos_item := 1; lookaheads_item := lookahead_set_5 |} ]%list.
Extract Inlined Constant items_of_state_25 => "assert false".

Definition items_of_state_26 : list item :=
  [ {| prod_item := Prod'patterncharacter'9; dot_pos_item := 1; lookaheads_item := lookahead_set_5 |} ]%list.
Extract Inlined Constant items_of_state_26 => "assert false".

Definition items_of_state_27 : list item :=
  [ {| prod_item := Prod'patterncharacter'3; dot_pos_item := 1; lookaheads_item := lookahead_set_5 |} ]%list.
Extract Inlined Constant items_of_state_27 => "assert false".

Definition items_of_state_28 : list item :=
  [ {| prod_item := Prod'patterncharacter'1; dot_pos_item := 1; lookaheads_item := lookahead_set_5 |} ]%list.
Extract Inlined Constant items_of_state_28 => "assert false".

Definition items_of_state_29 : list item :=
  [ {| prod_item := Prod'patterncharacter'21; dot_pos_item := 1; lookaheads_item := lookahead_set_5 |} ]%list.
Extract Inlined Constant items_of_state_29 => "assert false".

Definition items_of_state_30 : list item :=
  [ {| prod_item := Prod'patterncharacter'28; dot_pos_item := 1; lookaheads_item := lookahead_set_5 |} ]%list.
Extract Inlined Constant items_of_state_30 => "assert false".

Definition items_of_state_31 : list item :=
  [ {| prod_item := Prod'patterncharacter'26; dot_pos_item := 1; lookaheads_item := lookahead_set_5 |} ]%list.
Extract Inlined Constant items_of_state_31 => "assert false".

Definition items_of_state_32 : list item :=
  [ {| prod_item := Prod'patterncharacter'25; dot_pos_item := 1; lookaheads_item := lookahead_set_5 |} ]%list.
Extract Inlined Constant items_of_state_32 => "assert false".

Definition items_of_state_33 : list item :=
  [ {| prod_item := Prod'patterncharacter'23; dot_pos_item := 1; lookaheads_item := lookahead_set_5 |} ]%list.
Extract Inlined Constant items_of_state_33 => "assert false".

Definition items_of_state_34 : list item :=
  [ {| prod_item := Prod'atom'1; dot_pos_item := 1; lookaheads_item := lookahead_set_5 |} ]%list.
Extract Inlined Constant items_of_state_34 => "assert false".

Definition items_of_state_35 : list item :=
  [ {| prod_item := Prod'patterncharacter'19; dot_pos_item := 1; lookaheads_item := lookahead_set_5 |} ]%list.
Extract Inlined Constant items_of_state_35 => "assert false".

Definition items_of_state_36 : list item :=
  [ {| prod_item := Prod'patterncharacter'20; dot_pos_item := 1; lookaheads_item := lookahead_set_5 |} ]%list.
Extract Inlined Constant items_of_state_36 => "assert false".

Definition items_of_state_37 : list item :=
  [ {| prod_item := Prod'patterncharacter'0; dot_pos_item := 1; lookaheads_item := lookahead_set_5 |} ]%list.
Extract Inlined Constant items_of_state_37 => "assert false".

Definition items_of_state_38 : list item :=
  [ {| prod_item := Prod'alternative'1; dot_pos_item := 1; lookaheads_item := lookahead_set_6 |} ]%list.
Extract Inlined Constant items_of_state_38 => "assert false".

Definition items_of_state_39 : list item :=
  [ {| prod_item := Prod'atom'0; dot_pos_item := 1; lookaheads_item := lookahead_set_5 |} ]%list.
Extract Inlined Constant items_of_state_39 => "assert false".

Definition items_of_state_40 : list item :=
  [ {| prod_item := Prod'assertion'3; dot_pos_item := 5; lookaheads_item := lookahead_set_6 |} ]%list.
Extract Inlined Constant items_of_state_40 => "assert false".

Definition items_of_state_41 : list item :=
  [ {| prod_item := Prod'assertion'3; dot_pos_item := 6; lookaheads_item := lookahead_set_6 |} ]%list.
Extract Inlined Constant items_of_state_41 => "assert false".

Definition items_of_state_42 : list item :=
  [ {| prod_item := Prod'patterncharacter'30; dot_pos_item := 1; lookaheads_item := lookahead_set_5 |} ]%list.
Extract Inlined Constant items_of_state_42 => "assert false".

Definition items_of_state_43 : list item :=
  [ {| prod_item := Prod'quantifier'0; dot_pos_item := 0; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'quantifier'1; dot_pos_item := 0; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'quantifier'2; dot_pos_item := 0; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'quantifier'3; dot_pos_item := 0; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'quantifier'4; dot_pos_item := 0; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'quantifier'5; dot_pos_item := 0; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'quantifier'6; dot_pos_item := 0; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'quantifier'7; dot_pos_item := 0; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'quantifier'8; dot_pos_item := 0; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'quantifier'9; dot_pos_item := 0; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'quantifier'10; dot_pos_item := 0; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'quantifier'11; dot_pos_item := 0; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'term'1; dot_pos_item := 1; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'term'2; dot_pos_item := 1; lookaheads_item := lookahead_set_6 |} ]%list.
Extract Inlined Constant items_of_state_43 => "assert false".

Definition items_of_state_44 : list item :=
  [ {| prod_item := Prod'quantifier'0; dot_pos_item := 1; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'quantifier'1; dot_pos_item := 1; lookaheads_item := lookahead_set_6 |} ]%list.
Extract Inlined Constant items_of_state_44 => "assert false".

Definition items_of_state_45 : list item :=
  [ {| prod_item := Prod'quantifier'1; dot_pos_item := 2; lookaheads_item := lookahead_set_6 |} ]%list.
Extract Inlined Constant items_of_state_45 => "assert false".

Definition items_of_state_46 : list item :=
  [ {| prod_item := Prod'quantifier'4; dot_pos_item := 1; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'quantifier'5; dot_pos_item := 1; lookaheads_item := lookahead_set_6 |} ]%list.
Extract Inlined Constant items_of_state_46 => "assert false".

Definition items_of_state_47 : list item :=
  [ {| prod_item := Prod'quantifier'5; dot_pos_item := 2; lookaheads_item := lookahead_set_6 |} ]%list.
Extract Inlined Constant items_of_state_47 => "assert false".

Definition items_of_state_48 : list item :=
  [ {| prod_item := Prod'quantifier'2; dot_pos_item := 1; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'quantifier'3; dot_pos_item := 1; lookaheads_item := lookahead_set_6 |} ]%list.
Extract Inlined Constant items_of_state_48 => "assert false".

Definition items_of_state_49 : list item :=
  [ {| prod_item := Prod'quantifier'3; dot_pos_item := 2; lookaheads_item := lookahead_set_6 |} ]%list.
Extract Inlined Constant items_of_state_49 => "assert false".

Definition items_of_state_50 : list item :=
  [ {| prod_item := Prod'decimaldigit'0; dot_pos_item := 0; lookaheads_item := lookahead_set_10 |};
    {| prod_item := Prod'decimaldigit'1; dot_pos_item := 0; lookaheads_item := lookahead_set_10 |};
    {| prod_item := Prod'decimaldigits'0; dot_pos_item := 0; lookaheads_item := lookahead_set_11 |};
    {| prod_item := Prod'decimaldigits_'0; dot_pos_item := 0; lookaheads_item := lookahead_set_10 |};
    {| prod_item := Prod'decimaldigits_'1; dot_pos_item := 0; lookaheads_item := lookahead_set_10 |};
    {| prod_item := Prod'quantifier'6; dot_pos_item := 1; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'quantifier'7; dot_pos_item := 1; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'quantifier'8; dot_pos_item := 1; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'quantifier'9; dot_pos_item := 1; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'quantifier'10; dot_pos_item := 1; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'quantifier'11; dot_pos_item := 1; lookaheads_item := lookahead_set_6 |} ]%list.
Extract Inlined Constant items_of_state_50 => "assert false".

Definition items_of_state_51 : list item :=
  [ {| prod_item := Prod'decimaldigit'0; dot_pos_item := 0; lookaheads_item := lookahead_set_10 |};
    {| prod_item := Prod'decimaldigit'1; dot_pos_item := 0; lookaheads_item := lookahead_set_10 |};
    {| prod_item := Prod'decimaldigits'0; dot_pos_item := 1; lookaheads_item := lookahead_set_11 |};
    {| prod_item := Prod'decimaldigits_'0; dot_pos_item := 1; lookaheads_item := lookahead_set_10 |} ]%list.
Extract Inlined Constant items_of_state_51 => "assert false".

Definition items_of_state_52 : list item :=
  [ {| prod_item := Prod'decimaldigits_'0; dot_pos_item := 2; lookaheads_item := lookahead_set_10 |} ]%list.
Extract Inlined Constant items_of_state_52 => "assert false".

Definition items_of_state_53 : list item :=
  [ {| prod_item := Prod'quantifier'6; dot_pos_item := 2; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'quantifier'7; dot_pos_item := 2; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'quantifier'8; dot_pos_item := 2; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'quantifier'9; dot_pos_item := 2; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'quantifier'10; dot_pos_item := 2; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'quantifier'11; dot_pos_item := 2; lookaheads_item := lookahead_set_6 |} ]%list.
Extract Inlined Constant items_of_state_53 => "assert false".

Definition items_of_state_54 : list item :=
  [ {| prod_item := Prod'quantifier'6; dot_pos_item := 3; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'quantifier'7; dot_pos_item := 3; lookaheads_item := lookahead_set_6 |} ]%list.
Extract Inlined Constant items_of_state_54 => "assert false".

Definition items_of_state_55 : list item :=
  [ {| prod_item := Prod'quantifier'7; dot_pos_item := 4; lookaheads_item := lookahead_set_6 |} ]%list.
Extract Inlined Constant items_of_state_55 => "assert false".

Definition items_of_state_56 : list item :=
  [ {| prod_item := Prod'decimaldigit'0; dot_pos_item := 0; lookaheads_item := lookahead_set_12 |};
    {| prod_item := Prod'decimaldigit'1; dot_pos_item := 0; lookaheads_item := lookahead_set_12 |};
    {| prod_item := Prod'decimaldigits'0; dot_pos_item := 0; lookaheads_item := lookahead_set_13 |};
    {| prod_item := Prod'decimaldigits_'0; dot_pos_item := 0; lookaheads_item := lookahead_set_12 |};
    {| prod_item := Prod'decimaldigits_'1; dot_pos_item := 0; lookaheads_item := lookahead_set_12 |};
    {| prod_item := Prod'quantifier'8; dot_pos_item := 3; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'quantifier'9; dot_pos_item := 3; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'quantifier'10; dot_pos_item := 3; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'quantifier'11; dot_pos_item := 3; lookaheads_item := lookahead_set_6 |} ]%list.
Extract Inlined Constant items_of_state_56 => "assert false".

Definition items_of_state_57 : list item :=
  [ {| prod_item := Prod'quantifier'8; dot_pos_item := 4; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'quantifier'9; dot_pos_item := 4; lookaheads_item := lookahead_set_6 |} ]%list.
Extract Inlined Constant items_of_state_57 => "assert false".

Definition items_of_state_58 : list item :=
  [ {| prod_item := Prod'quantifier'9; dot_pos_item := 5; lookaheads_item := lookahead_set_6 |} ]%list.
Extract Inlined Constant items_of_state_58 => "assert false".

Definition items_of_state_59 : list item :=
  [ {| prod_item := Prod'quantifier'10; dot_pos_item := 4; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'quantifier'11; dot_pos_item := 4; lookaheads_item := lookahead_set_6 |} ]%list.
Extract Inlined Constant items_of_state_59 => "assert false".

Definition items_of_state_60 : list item :=
  [ {| prod_item := Prod'quantifier'10; dot_pos_item := 5; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'quantifier'11; dot_pos_item := 5; lookaheads_item := lookahead_set_6 |} ]%list.
Extract Inlined Constant items_of_state_60 => "assert false".

Definition items_of_state_61 : list item :=
  [ {| prod_item := Prod'quantifier'11; dot_pos_item := 6; lookaheads_item := lookahead_set_6 |} ]%list.
Extract Inlined Constant items_of_state_61 => "assert false".

Definition items_of_state_62 : list item :=
  [ {| prod_item := Prod'decimaldigits_'1; dot_pos_item := 1; lookaheads_item := lookahead_set_10 |} ]%list.
Extract Inlined Constant items_of_state_62 => "assert false".

Definition items_of_state_63 : list item :=
  [ {| prod_item := Prod'term'2; dot_pos_item := 2; lookaheads_item := lookahead_set_6 |} ]%list.
Extract Inlined Constant items_of_state_63 => "assert false".

Definition items_of_state_64 : list item :=
  [ {| prod_item := Prod'term'0; dot_pos_item := 1; lookaheads_item := lookahead_set_6 |} ]%list.
Extract Inlined Constant items_of_state_64 => "assert false".

Definition items_of_state_65 : list item :=
  [ {| prod_item := Prod'alternative'0; dot_pos_item := 1; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'assertion'0; dot_pos_item := 0; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'assertion'1; dot_pos_item := 0; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'assertion'2; dot_pos_item := 0; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'assertion'3; dot_pos_item := 0; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'atom'0; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'atom'1; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'decimaldigit'0; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'decimaldigit'1; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'disjunction'0; dot_pos_item := 1; lookaheads_item := lookahead_set_14 |};
    {| prod_item := Prod'disjunction'1; dot_pos_item := 1; lookaheads_item := lookahead_set_14 |};
    {| prod_item := Prod'patterncharacter'0; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'patterncharacter'1; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'patterncharacter'2; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'patterncharacter'3; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'patterncharacter'4; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'patterncharacter'5; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'patterncharacter'6; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'patterncharacter'7; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'patterncharacter'8; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'patterncharacter'9; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'patterncharacter'10; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'patterncharacter'11; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'patterncharacter'12; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'patterncharacter'13; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'patterncharacter'14; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'patterncharacter'15; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'patterncharacter'16; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'patterncharacter'17; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'patterncharacter'18; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'patterncharacter'19; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'patterncharacter'20; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'patterncharacter'21; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'patterncharacter'22; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'patterncharacter'23; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'patterncharacter'24; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'patterncharacter'25; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'patterncharacter'26; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'patterncharacter'27; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'patterncharacter'28; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'patterncharacter'29; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'patterncharacter'30; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'term'0; dot_pos_item := 0; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'term'1; dot_pos_item := 0; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'term'2; dot_pos_item := 0; lookaheads_item := lookahead_set_6 |} ]%list.
Extract Inlined Constant items_of_state_65 => "assert false".

Definition items_of_state_66 : list item :=
  [ {| prod_item := Prod'alternative'0; dot_pos_item := 0; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'alternative'1; dot_pos_item := 0; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'alternative'2; dot_pos_item := 0; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'assertion'0; dot_pos_item := 0; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'assertion'1; dot_pos_item := 0; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'assertion'2; dot_pos_item := 0; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'assertion'3; dot_pos_item := 0; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'atom'0; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'atom'1; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'decimaldigit'0; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'decimaldigit'1; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'disjunction'0; dot_pos_item := 0; lookaheads_item := lookahead_set_14 |};
    {| prod_item := Prod'disjunction'1; dot_pos_item := 0; lookaheads_item := lookahead_set_14 |};
    {| prod_item := Prod'disjunction'1; dot_pos_item := 2; lookaheads_item := lookahead_set_14 |};
    {| prod_item := Prod'patterncharacter'0; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'patterncharacter'1; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'patterncharacter'2; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'patterncharacter'3; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'patterncharacter'4; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'patterncharacter'5; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'patterncharacter'6; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'patterncharacter'7; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'patterncharacter'8; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'patterncharacter'9; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'patterncharacter'10; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'patterncharacter'11; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'patterncharacter'12; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'patterncharacter'13; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'patterncharacter'14; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'patterncharacter'15; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'patterncharacter'16; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'patterncharacter'17; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'patterncharacter'18; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'patterncharacter'19; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'patterncharacter'20; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'patterncharacter'21; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'patterncharacter'22; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'patterncharacter'23; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'patterncharacter'24; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'patterncharacter'25; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'patterncharacter'26; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'patterncharacter'27; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'patterncharacter'28; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'patterncharacter'29; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'patterncharacter'30; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'term'0; dot_pos_item := 0; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'term'1; dot_pos_item := 0; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'term'2; dot_pos_item := 0; lookaheads_item := lookahead_set_6 |} ]%list.
Extract Inlined Constant items_of_state_66 => "assert false".

Definition items_of_state_67 : list item :=
  [ {| prod_item := Prod'disjunction'1; dot_pos_item := 3; lookaheads_item := lookahead_set_14 |} ]%list.
Extract Inlined Constant items_of_state_67 => "assert false".

Definition items_of_state_68 : list item :=
  [ {| prod_item := Prod'alternative'0; dot_pos_item := 2; lookaheads_item := lookahead_set_6 |} ]%list.
Extract Inlined Constant items_of_state_68 => "assert false".

Definition items_of_state_69 : list item :=
  [ {| prod_item := Prod'alternative'0; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |};
    {| prod_item := Prod'alternative'1; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |};
    {| prod_item := Prod'alternative'2; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |};
    {| prod_item := Prod'assertion'0; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |};
    {| prod_item := Prod'assertion'1; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |};
    {| prod_item := Prod'assertion'2; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |};
    {| prod_item := Prod'assertion'2; dot_pos_item := 4; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'assertion'3; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |};
    {| prod_item := Prod'atom'0; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'atom'1; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'decimaldigit'0; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'decimaldigit'1; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'disjunction'0; dot_pos_item := 0; lookaheads_item := lookahead_set_9 |};
    {| prod_item := Prod'disjunction'1; dot_pos_item := 0; lookaheads_item := lookahead_set_9 |};
    {| prod_item := Prod'patterncharacter'0; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'1; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'2; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'3; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'4; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'5; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'6; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'7; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'8; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'9; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'10; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'11; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'12; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'13; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'14; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'15; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'16; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'17; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'18; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'19; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'20; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'21; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'22; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'23; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'24; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'25; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'26; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'27; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'28; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'29; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'30; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'term'0; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |};
    {| prod_item := Prod'term'1; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |};
    {| prod_item := Prod'term'2; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |} ]%list.
Extract Inlined Constant items_of_state_69 => "assert false".

Definition items_of_state_70 : list item :=
  [ {| prod_item := Prod'assertion'2; dot_pos_item := 5; lookaheads_item := lookahead_set_6 |} ]%list.
Extract Inlined Constant items_of_state_70 => "assert false".

Definition items_of_state_71 : list item :=
  [ {| prod_item := Prod'assertion'2; dot_pos_item := 6; lookaheads_item := lookahead_set_6 |} ]%list.
Extract Inlined Constant items_of_state_71 => "assert false".

Definition items_of_state_72 : list item :=
  [ {| prod_item := Prod'alternative'0; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |};
    {| prod_item := Prod'alternative'1; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |};
    {| prod_item := Prod'alternative'2; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |};
    {| prod_item := Prod'assertion'0; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |};
    {| prod_item := Prod'assertion'1; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |};
    {| prod_item := Prod'assertion'1; dot_pos_item := 3; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'assertion'2; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |};
    {| prod_item := Prod'assertion'3; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |};
    {| prod_item := Prod'atom'0; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'atom'1; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'decimaldigit'0; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'decimaldigit'1; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'disjunction'0; dot_pos_item := 0; lookaheads_item := lookahead_set_9 |};
    {| prod_item := Prod'disjunction'1; dot_pos_item := 0; lookaheads_item := lookahead_set_9 |};
    {| prod_item := Prod'patterncharacter'0; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'1; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'2; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'3; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'4; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'5; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'6; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'7; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'8; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'9; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'10; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'11; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'12; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'13; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'14; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'15; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'16; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'17; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'18; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'19; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'20; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'21; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'22; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'23; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'24; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'25; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'26; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'27; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'28; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'29; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'30; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'term'0; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |};
    {| prod_item := Prod'term'1; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |};
    {| prod_item := Prod'term'2; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |} ]%list.
Extract Inlined Constant items_of_state_72 => "assert false".

Definition items_of_state_73 : list item :=
  [ {| prod_item := Prod'assertion'1; dot_pos_item := 4; lookaheads_item := lookahead_set_6 |} ]%list.
Extract Inlined Constant items_of_state_73 => "assert false".

Definition items_of_state_74 : list item :=
  [ {| prod_item := Prod'assertion'1; dot_pos_item := 5; lookaheads_item := lookahead_set_6 |} ]%list.
Extract Inlined Constant items_of_state_74 => "assert false".

Definition items_of_state_75 : list item :=
  [ {| prod_item := Prod'alternative'0; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |};
    {| prod_item := Prod'alternative'1; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |};
    {| prod_item := Prod'alternative'2; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |};
    {| prod_item := Prod'assertion'0; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |};
    {| prod_item := Prod'assertion'0; dot_pos_item := 3; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'assertion'1; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |};
    {| prod_item := Prod'assertion'2; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |};
    {| prod_item := Prod'assertion'3; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |};
    {| prod_item := Prod'atom'0; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'atom'1; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'decimaldigit'0; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'decimaldigit'1; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'disjunction'0; dot_pos_item := 0; lookaheads_item := lookahead_set_9 |};
    {| prod_item := Prod'disjunction'1; dot_pos_item := 0; lookaheads_item := lookahead_set_9 |};
    {| prod_item := Prod'patterncharacter'0; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'1; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'2; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'3; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'4; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'5; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'6; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'7; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'8; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'9; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'10; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'11; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'12; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'13; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'14; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'15; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'16; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'17; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'18; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'19; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'20; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'21; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'22; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'23; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'24; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'25; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'26; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'27; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'28; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'29; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'patterncharacter'30; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'term'0; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |};
    {| prod_item := Prod'term'1; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |};
    {| prod_item := Prod'term'2; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |} ]%list.
Extract Inlined Constant items_of_state_75 => "assert false".

Definition items_of_state_76 : list item :=
  [ {| prod_item := Prod'assertion'0; dot_pos_item := 4; lookaheads_item := lookahead_set_6 |} ]%list.
Extract Inlined Constant items_of_state_76 => "assert false".

Definition items_of_state_77 : list item :=
  [ {| prod_item := Prod'assertion'0; dot_pos_item := 5; lookaheads_item := lookahead_set_6 |} ]%list.
Extract Inlined Constant items_of_state_77 => "assert false".

Definition items_of_state_78 : list item :=
  [ {| prod_item := Prod'main'0; dot_pos_item := 1; lookaheads_item := lookahead_set_4 |} ]%list.
Extract Inlined Constant items_of_state_78 => "assert false".

Definition items_of_state_79 : list item :=
  [ {| prod_item := Prod'main'0; dot_pos_item := 2; lookaheads_item := lookahead_set_4 |} ]%list.
Extract Inlined Constant items_of_state_79 => "assert false".

Definition items_of_state_81 : list item :=
  [ {| prod_item := Prod'pattern'0; dot_pos_item := 1; lookaheads_item := lookahead_set_3 |} ]%list.
Extract Inlined Constant items_of_state_81 => "assert false".

Definition items_of_state (s:state) : list item :=
  match s with
  | Init Init'0 => items_of_state_0
  | Ninit Nis'1 => items_of_state_1
  | Ninit Nis'2 => items_of_state_2
  | Ninit Nis'3 => items_of_state_3
  | Ninit Nis'4 => items_of_state_4
  | Ninit Nis'5 => items_of_state_5
  | Ninit Nis'6 => items_of_state_6
  | Ninit Nis'7 => items_of_state_7
  | Ninit Nis'8 => items_of_state_8
  | Ninit Nis'9 => items_of_state_9
  | Ninit Nis'10 => items_of_state_10
  | Ninit Nis'11 => items_of_state_11
  | Ninit Nis'12 => items_of_state_12
  | Ninit Nis'13 => items_of_state_13
  | Ninit Nis'14 => items_of_state_14
  | Ninit Nis'15 => items_of_state_15
  | Ninit Nis'16 => items_of_state_16
  | Ninit Nis'17 => items_of_state_17
  | Ninit Nis'18 => items_of_state_18
  | Ninit Nis'19 => items_of_state_19
  | Ninit Nis'20 => items_of_state_20
  | Ninit Nis'21 => items_of_state_21
  | Ninit Nis'22 => items_of_state_22
  | Ninit Nis'23 => items_of_state_23
  | Ninit Nis'24 => items_of_state_24
  | Ninit Nis'25 => items_of_state_25
  | Ninit Nis'26 => items_of_state_26
  | Ninit Nis'27 => items_of_state_27
  | Ninit Nis'28 => items_of_state_28
  | Ninit Nis'29 => items_of_state_29
  | Ninit Nis'30 => items_of_state_30
  | Ninit Nis'31 => items_of_state_31
  | Ninit Nis'32 => items_of_state_32
  | Ninit Nis'33 => items_of_state_33
  | Ninit Nis'34 => items_of_state_34
  | Ninit Nis'35 => items_of_state_35
  | Ninit Nis'36 => items_of_state_36
  | Ninit Nis'37 => items_of_state_37
  | Ninit Nis'38 => items_of_state_38
  | Ninit Nis'39 => items_of_state_39
  | Ninit Nis'40 => items_of_state_40
  | Ninit Nis'41 => items_of_state_41
  | Ninit Nis'42 => items_of_state_42
  | Ninit Nis'43 => items_of_state_43
  | Ninit Nis'44 => items_of_state_44
  | Ninit Nis'45 => items_of_state_45
  | Ninit Nis'46 => items_of_state_46
  | Ninit Nis'47 => items_of_state_47
  | Ninit Nis'48 => items_of_state_48
  | Ninit Nis'49 => items_of_state_49
  | Ninit Nis'50 => items_of_state_50
  | Ninit Nis'51 => items_of_state_51
  | Ninit Nis'52 => items_of_state_52
  | Ninit Nis'53 => items_of_state_53
  | Ninit Nis'54 => items_of_state_54
  | Ninit Nis'55 => items_of_state_55
  | Ninit Nis'56 => items_of_state_56
  | Ninit Nis'57 => items_of_state_57
  | Ninit Nis'58 => items_of_state_58
  | Ninit Nis'59 => items_of_state_59
  | Ninit Nis'60 => items_of_state_60
  | Ninit Nis'61 => items_of_state_61
  | Ninit Nis'62 => items_of_state_62
  | Ninit Nis'63 => items_of_state_63
  | Ninit Nis'64 => items_of_state_64
  | Ninit Nis'65 => items_of_state_65
  | Ninit Nis'66 => items_of_state_66
  | Ninit Nis'67 => items_of_state_67
  | Ninit Nis'68 => items_of_state_68
  | Ninit Nis'69 => items_of_state_69
  | Ninit Nis'70 => items_of_state_70
  | Ninit Nis'71 => items_of_state_71
  | Ninit Nis'72 => items_of_state_72
  | Ninit Nis'73 => items_of_state_73
  | Ninit Nis'74 => items_of_state_74
  | Ninit Nis'75 => items_of_state_75
  | Ninit Nis'76 => items_of_state_76
  | Ninit Nis'77 => items_of_state_77
  | Ninit Nis'78 => items_of_state_78
  | Ninit Nis'79 => items_of_state_79
  | Ninit Nis'81 => items_of_state_81
  end.
Extract Constant items_of_state => "fun _ -> assert false".

Definition N_of_state (s:state) : N :=
  match s with
  | Init Init'0 => 0%N
  | Ninit Nis'1 => 1%N
  | Ninit Nis'2 => 2%N
  | Ninit Nis'3 => 3%N
  | Ninit Nis'4 => 4%N
  | Ninit Nis'5 => 5%N
  | Ninit Nis'6 => 6%N
  | Ninit Nis'7 => 7%N
  | Ninit Nis'8 => 8%N
  | Ninit Nis'9 => 9%N
  | Ninit Nis'10 => 10%N
  | Ninit Nis'11 => 11%N
  | Ninit Nis'12 => 12%N
  | Ninit Nis'13 => 13%N
  | Ninit Nis'14 => 14%N
  | Ninit Nis'15 => 15%N
  | Ninit Nis'16 => 16%N
  | Ninit Nis'17 => 17%N
  | Ninit Nis'18 => 18%N
  | Ninit Nis'19 => 19%N
  | Ninit Nis'20 => 20%N
  | Ninit Nis'21 => 21%N
  | Ninit Nis'22 => 22%N
  | Ninit Nis'23 => 23%N
  | Ninit Nis'24 => 24%N
  | Ninit Nis'25 => 25%N
  | Ninit Nis'26 => 26%N
  | Ninit Nis'27 => 27%N
  | Ninit Nis'28 => 28%N
  | Ninit Nis'29 => 29%N
  | Ninit Nis'30 => 30%N
  | Ninit Nis'31 => 31%N
  | Ninit Nis'32 => 32%N
  | Ninit Nis'33 => 33%N
  | Ninit Nis'34 => 34%N
  | Ninit Nis'35 => 35%N
  | Ninit Nis'36 => 36%N
  | Ninit Nis'37 => 37%N
  | Ninit Nis'38 => 38%N
  | Ninit Nis'39 => 39%N
  | Ninit Nis'40 => 40%N
  | Ninit Nis'41 => 41%N
  | Ninit Nis'42 => 42%N
  | Ninit Nis'43 => 43%N
  | Ninit Nis'44 => 44%N
  | Ninit Nis'45 => 45%N
  | Ninit Nis'46 => 46%N
  | Ninit Nis'47 => 47%N
  | Ninit Nis'48 => 48%N
  | Ninit Nis'49 => 49%N
  | Ninit Nis'50 => 50%N
  | Ninit Nis'51 => 51%N
  | Ninit Nis'52 => 52%N
  | Ninit Nis'53 => 53%N
  | Ninit Nis'54 => 54%N
  | Ninit Nis'55 => 55%N
  | Ninit Nis'56 => 56%N
  | Ninit Nis'57 => 57%N
  | Ninit Nis'58 => 58%N
  | Ninit Nis'59 => 59%N
  | Ninit Nis'60 => 60%N
  | Ninit Nis'61 => 61%N
  | Ninit Nis'62 => 62%N
  | Ninit Nis'63 => 63%N
  | Ninit Nis'64 => 64%N
  | Ninit Nis'65 => 65%N
  | Ninit Nis'66 => 66%N
  | Ninit Nis'67 => 67%N
  | Ninit Nis'68 => 68%N
  | Ninit Nis'69 => 69%N
  | Ninit Nis'70 => 70%N
  | Ninit Nis'71 => 71%N
  | Ninit Nis'72 => 72%N
  | Ninit Nis'73 => 73%N
  | Ninit Nis'74 => 74%N
  | Ninit Nis'75 => 75%N
  | Ninit Nis'76 => 76%N
  | Ninit Nis'77 => 77%N
  | Ninit Nis'78 => 78%N
  | Ninit Nis'79 => 79%N
  | Ninit Nis'81 => 81%N
  end.
End Aut.

Module MenhirLibParser := MenhirLib.Main.Make Aut.
Theorem safe:
  MenhirLibParser.safe_validator tt = true.
Proof eq_refl true<:MenhirLibParser.safe_validator tt = true.

Theorem complete:
  MenhirLibParser.complete_validator tt = true.
Proof eq_refl true<:MenhirLibParser.complete_validator tt = true.

Definition main : nat -> MenhirLibParser.Inter.buffer -> MenhirLibParser.Inter.parse_result        (Warblre.Extracted.Patterns.coq_Regex) := MenhirLibParser.parse safe Aut.Init'0.

Theorem main_correct (log_fuel : nat) (buffer : MenhirLibParser.Inter.buffer):
  match main log_fuel buffer with
  | MenhirLibParser.Inter.Parsed_pr sem buffer_new =>
      exists word (tree : Gram.parse_tree (NT main'nt) word),
        buffer = MenhirLibParser.Inter.app_buf word buffer_new /\
        Gram.pt_sem tree = sem
  | _ => True
  end.
Proof. apply MenhirLibParser.parse_correct with (init:=Aut.Init'0). Qed.

Theorem main_complete (log_fuel : nat) (word : list token) (buffer_end : MenhirLibParser.Inter.buffer) :
  forall tree : Gram.parse_tree (NT main'nt) word,
  match main log_fuel (MenhirLibParser.Inter.app_buf word buffer_end) with
  | MenhirLibParser.Inter.Fail_pr => False
  | MenhirLibParser.Inter.Parsed_pr output_res buffer_end_res =>
      output_res = Gram.pt_sem tree /\
      buffer_end_res = buffer_end /\ (Gram.pt_size tree <= PeanoNat.Nat.pow 2 log_fuel)%nat
  | MenhirLibParser.Inter.Timeout_pr => (PeanoNat.Nat.pow 2 log_fuel < Gram.pt_size tree)%nat
  end.
Proof. apply MenhirLibParser.parse_complete with (init:=Aut.Init'0); exact complete. Qed.




