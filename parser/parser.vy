%token <char> CHAR
%token <char> NZDIGIT
%token ALT
%token LPAR RPAR
%token LBRAC RBRAC COMMA
%token LBRACK RBRACK
%token STAR PLUS QMARK
%token HAT DOLLAR BACKSL DOT
%token COLONS LESS MORE EQUAL MINUS EXCL
%token LOWB UPB LOWD UPD LOWS UPS LOWW UPW
%token LOWF LOWN LOWR LOWT LOWV LOWK LOWX LOWU LOWP UPP
%token ZERO
%token EOF

%start <Warblre.Extracted.Patterns.coq_Regex> main
%type  <char> decimaldigit
%type  <string> decimaldigits_
%type  <int> decimaldigits
%type  <char> patterncharacter
%type  <char> syntaxcharacter
%type  <Warblre.Extracted.Patterns.coq_Regex> pattern
%type  <Warblre.Extracted.Patterns.coq_Regex> disjunction
%type  <Warblre.Extracted.Patterns.coq_Regex> alternative
%type  <Warblre.Extracted.Patterns.coq_Regex> term
%type  <Warblre.Extracted.Patterns.coq_Regex> assertion
%type  <Warblre.Extracted.Patterns.coq_Regex> atom
%type  <Warblre.Extracted.Patterns.coq_Regex> atomescape
%type  <Warblre.Extracted.Patterns.coq_Quantifier> quantifier
%type  <Charclasses.char_group> characterclassescape
%type  <char> characterescape
%type  <char> controlescape
%type  <char> identityescape
%type  <string> decimalescape
%type  <Warblre.Extracted.Patterns.character> characterclass
%type  <Charclasses.char_class> classcontents
%type  <Charclasses.char_class> nonemptyclassranges
%type  <Charclasses.char_class> nonemptyclassrangesnodash
%type  <Charclasses.char_class_elt> classatomnodash
%type  <char> classatomnodashchar
%type  <Charclasses.char_class_elt> classatom
%type  <Charclasses.char_class_elt> classescape

%%

decimaldigit:
  | nz=NZDIGIT { nz }
  | ZERO { '0' }

decimaldigits_:
  | d1=decimaldigits_ d2=decimaldigit { d1 ^ String.make 1 d2 }
  | d=decimaldigit { String.make 1 d }
  
decimaldigits:
  | d=decimaldigits_ { int_of_string d }

/* https://tc39.es/ecma262/#sec-patterns */

main: r=pattern EOF { r }

pattern:
  | d=disjunction { d }

disjunction:
  | a=alternative { a }
  | a=alternative ALT d=disjunction { Warblre.Extracted.Patterns.Disjunction(a,d) }

alternative:
  | a=alternative t=term { Warblre.Extracted.Patterns.Seq(a,t) }
  | t=term { t } /* differs from the spec here */
  | { Warblre.Extracted.Patterns.Empty }

term:
  | a=assertion { a }
  | a=atom { a }
  | a=atom q=quantifier { Warblre.Extracted.Patterns.Quantified(a,q) }
/* separation between usual quantifier and counted ones since they are separate in the OCaml engine AST. Could be changed if needed */

assertion:
//   | HAT { Raw_anchor(BeginInput) }
//   | DOLLAR { Raw_anchor(EndInput) }
//   | BACKSL LOWB { Raw_anchor(WordBoundary) }
//   | BACKSL UPB { Raw_anchor(NonWordBoundary) }
  | LPAR QMARK EQUAL d=disjunction RPAR { Warblre.Extracted.Patterns.Lookahead(d) }
  | LPAR QMARK EXCL d=disjunction RPAR { Warblre.Extracted.Patterns.NegativeLookahead(d) }
  | LPAR QMARK LESS EQUAL d=disjunction RPAR { Warblre.Extracted.Patterns.Lookbehind(d) }
  | LPAR QMARK LESS EXCL d=disjunction RPAR { Warblre.Extracted.Patterns.NegativeLookbehind(d) }

quantifier:
  | STAR { Warblre.Extracted.Patterns.Greedy(Warblre.Extracted.Patterns.Star) }
  | STAR QMARK { Warblre.Extracted.Patterns.Lazy(Warblre.Extracted.Patterns.Star) }
  | PLUS { Warblre.Extracted.Patterns.Greedy(Warblre.Extracted.Patterns.Plus) }
  | PLUS QMARK { Warblre.Extracted.Patterns.Lazy(Warblre.Extracted.Patterns.Plus) }
  | QMARK { Warblre.Extracted.Patterns.Greedy(Warblre.Extracted.Patterns.Question) }
  | QMARK QMARK { Warblre.Extracted.Patterns.Lazy(Warblre.Extracted.Patterns.Question) }
  | LBRAC d=decimaldigits RBRAC { Warblre.Extracted.Patterns.Greedy(Warblre.Extracted.Patterns.RepExact(d)) }
  | LBRAC d=decimaldigits RBRAC QMARK{ Warblre.Extracted.Patterns.Lazy(Warblre.Extracted.Patterns.RepExact(d)) }
  | LBRAC d=decimaldigits COMMA RBRAC { Warblre.Extracted.Patterns.Greedy(Warblre.Extracted.Patterns.RepPartialRange(d)) }
  | LBRAC d=decimaldigits COMMA RBRAC QMARK { Warblre.Extracted.Patterns.Lazy(Warblre.Extracted.Patterns.RepPartialRange(d)) }
  | LBRAC dmin=decimaldigits COMMA dmax=decimaldigits RBRAC { Warblre.Extracted.Patterns.Greedy(Warblre.Extracted.Patterns.RepRange(dmin,dmax)) }
  | LBRAC dmin=decimaldigits COMMA dmax=decimaldigits RBRAC QMARK { Warblre.Extracted.Patterns.Lazy(Warblre.Extracted.Patterns.RepRange(dmin,dmax)) }

atom:
  | c=patterncharacter { Warblre.Extracted.Patterns.Char(c) }  
/* TODO: { for instance can be parsed as single char. But not (. I'm not sure where this is in the spec. Also I'm not sure why, if I add a similar rule for LBRAC, it does not work */
  | DOT { Warblre.Extracted.Patterns.Dot }
//   | BACKSL a=atomescape { a }
//   | c=characterclass { Raw_character c }
//   | LPAR d=disjunction RPAR { Raw_capture d }
/* TODO: fail if there is a group specifier */
//   | LPAR QMARK COLONS d=disjunction RPAR { d }

syntaxcharacter:
  | HAT { '^' }
  | DOLLAR { '$' }
  | BACKSL { '\\' }
  | DOT { '.' }
  | STAR { '*' }
  | PLUS { '+' }
  | QMARK { '?' }
  | LPAR { '(' }
  | RPAR { ')' }
  | LBRACK { '[' }
  | RBRACK { ']' }
  | LBRAC { '{' }
  | RBRAC { '}' }
  | ALT { '|' }

patterncharacter:
  | c=CHAR { c }
/* also adding all tokens that can be parsed as single characters */
  | LOWB { 'b' }
  | UPB { 'B' }
  | LOWD { 'd' }
  | UPD { 'D' }
  | LOWS { 's' }
  | UPS { 'S' }
  | LOWW { 'w' }
  | UPW { 'W' }
  | LOWF { 'f' }
  | LOWN { 'n' }
  | LOWR { 'r' }
  | LOWT { 't' }
  | LOWV { 'v' }
  | LOWK { 'k' }
  | LOWX { 'x' }
  | LOWU { 'u' }
  | LOWP { 'p' }
  | UPP { 'P' }
  | COMMA { ',' }
  | COLONS { ':' }
  | LESS { '<' }
  | MORE { '>' }
  | EQUAL { '=' }
  | MINUS { '-' }
  | EXCL { '!' }
  | LBRAC { '{' }
  | RBRAC { '}' }
/* TODO: still a bug when parsing for instance a{ */
  | LBRACK { '[' }
  | RBRACK { ']' } 
  | d=decimaldigit { d }


atomescape:
  | d=decimalescape { raise Warblre.Extracted.Patterns.Unsupported_backref }
  | c=characterclassescape { Raw_character(Group c) }
  | c=characterescape { Raw_character(Char c) }
  | LOWK { raise Warblre.Extracted.Patterns.Unsupported_named_groups }

characterescape:
  | c=controlescape { c }
  | ZERO { char_of_int 0 }
/* TODO: actually before raising the exception, it depends if there is a hexdigit sequence after the x, otherwise should be read as character x */
  | LOWX { raise Warblre.Extracted.Patterns.Unsupported_hex }
  | LOWU { raise Warblre.Extracted.Patterns.Unsupported_unicode }
  | i=identityescape { i }

controlescape:
  | LOWF { '\x0C' }
  | LOWN { '\n' }
  | LOWR { '\r' }
  | LOWT { '\t' }
  | LOWV { char_of_int 11 }

identityescape:
  | s=syntaxcharacter { s }
/* all other characters that represent themselves when escaped */
  | c=CHAR { c }
  | COMMA { ',' }
  | COLONS { ':' }
  | LESS { '<' }
  | MORE { '>' }
  | EQUAL { '=' }
  | MINUS { '-' }
  | EXCL { '!' }

decimalescape:
  | nz=NZDIGIT d=decimaldigits { String.make 1 nz ^ d }
  | nz=NZDIGIT { String.make 1 nz }

characterclassescape:
  | LOWD { Digit }
  | UPD { NonDigit }
  | LOWS { Space }
  | UPS { NonSpace }
  | LOWW { Word }
  | UPW { NonWord }
  | LOWP { raise Warblre.Extracted.Patterns.Unsupported_prop }
  | UPP { raise Warblre.Extracted.Patterns.Unsupported_prop }

characterclass:
  | LBRACK HAT c=classcontents RBRACK { NegClass c }
  | LBRACK c=classcontents RBRACK { Class c }

classcontents:
  | { [] }
  | n=nonemptyclassranges { n }

nonemptyclassranges:
  | a=classatom { [a] }
  | a=classatom n=nonemptyclassrangesnodash { a::n }
  | a1=classatom MINUS a2=classatom c=classcontents { (Charclasses.make_range a1 a2) @ c }

nonemptyclassrangesnodash:
  | a=classatom { [a] }
  | a=classatomnodash n=nonemptyclassrangesnodash { a::n }
  | a1=classatomnodash MINUS a2=classatom c=classcontents { (Charclasses.make_range a1 a2) @ c }
  


/* I'm removing the character groups \s \w... */
/* and making it a special rule */
/* otherwise I'm not sure how to type it for ranges */
/* Note that there still is a bug with e.g [a-\d] */

classatom:
  | MINUS { CChar '-' }
  | c=classatomnodash { c }

classatomnodash:
  | BACKSL c=classescape { c }
  | c=classatomnodashchar { CChar c }

classatomnodashchar:
/* all characters except \, ] and - */
  | HAT { '^' }
  | DOLLAR { '$' }
  | DOT { '.' }
  | STAR { '*' }
  | PLUS { '+' }
  | QMARK { '?' }
  | LPAR { '(' }
  | RPAR { ')' }
  | LBRACK { '[' }
  | LBRAC { '{' }
  | RBRAC { '}' }
  | ALT { '|' }
  | c=CHAR { c }
  | LOWB { 'b' }
  | UPB { 'B' }
  | LOWD { 'd' }
  | UPD { 'D' }
  | LOWS { 's' }
  | UPS { 'S' }
  | LOWW { 'w' }
  | UPW { 'W' }
  | LOWF { 'f' }
  | LOWN { 'n' }
  | LOWR { 'r' }
  | LOWT { 't' }
  | LOWV { 'v' }
  | LOWK { 'k' }
  | LOWX { 'x' }
  | LOWU { 'u' }
  | LOWP { 'p' }
  | UPP { 'P' }
  | COMMA { ',' }
  | COLONS { ':' }
  | LESS { '<' }
  | MORE { '>' }
  | EQUAL { '=' }
  | EXCL { '!' }
  | d=decimaldigit { d }

classescape:
  | LOWB { CChar (char_of_int 8) }	/* basckspace ascii character */
  | c=characterclassescape { CGroup c }
  | c=characterescape  { CChar c }
  | d=decimalescape { raise Warblre.Extracted.Patterns.Unsupported_octal }


%%

