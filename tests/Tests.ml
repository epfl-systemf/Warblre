open Warblre.Notations.UnicodeNotations
open Warblre.Testing.UnicodeTester

let%expect_test "char_class_atom_0_pos" =
  test_regex
    (CharacterClass (NoninvertedCC (ClassAtomCR (sc 'a', EmptyCR))))
    "abbb"
    0 ();
  [%expect {| Matched 1 characters ([0-1]) in 'abbb' (length=4) |}]

let%expect_test "char_class_atom_0_neg" =
  test_regex
    (CharacterClass (NoninvertedCC (ClassAtomCR (sc 'b', EmptyCR))))
    "abbb"
    0 ();
  [%expect {| No match on 'abbb' |}]

let%expect_test "negated_char_class_atom_0_pos" =
  test_regex
    (CharacterClass (InvertedCC (ClassAtomCR (sc 'b', EmptyCR))))
    "abbb"
    0 ();
  [%expect {| Matched 1 characters ([0-1]) in 'abbb' (length=4) |}]

let%expect_test "negated_char_class_atom_0_neg" =
  test_regex
    (CharacterClass (InvertedCC (ClassAtomCR (sc 'a', EmptyCR))))
    "abbb"
    0 ();
  [%expect {| No match on 'abbb' |}]




let%expect_test "char_class_seq_0_pos_0" =
  test_regex
    (CharacterClass (NoninvertedCC (RangeCR (sc 'a', sc 'c', EmptyCR))))
    "abbb"
    0 ();
  [%expect {| Matched 1 characters ([0-1]) in 'abbb' (length=4) |}]

let%expect_test "char_class_seq_0_pos_1" =
  test_regex
    (CharacterClass (NoninvertedCC (RangeCR (sc 'a', sc 'c', EmptyCR))))
    "bbbb"
    0 ();
  [%expect {| Matched 1 characters ([0-1]) in 'bbbb' (length=4) |}]

let%expect_test "char_class_seq_0_pos_2" =
  test_regex
    (CharacterClass (NoninvertedCC (RangeCR (sc 'a', sc 'c', EmptyCR))))
    "cbbb"
    0 ();
  [%expect {| Matched 1 characters ([0-1]) in 'cbbb' (length=4) |}]

let%expect_test "char_class_seq_0_neg_0" =
  test_regex
    (CharacterClass (NoninvertedCC (RangeCR (sc 'a', sc 'c', EmptyCR))))
    " bbb"
    0 ();
  [%expect {| No match on ' bbb' |}]

let%expect_test "char_class_seq_0_neg_1" =
  test_regex
    (CharacterClass (NoninvertedCC (RangeCR (sc 'a', sc 'c', EmptyCR))))
    "dbbb"
    0 ();
  [%expect {| No match on 'dbbb' |}]





let%expect_test "negated_char_class_seq_0_neg_0" =
  test_regex
    (CharacterClass (InvertedCC (RangeCR (sc 'a', sc 'c', EmptyCR))))
    "abbb"
    0 ();
  [%expect {| No match on 'abbb' |}]

let%expect_test "negated_char_class_seq_0_neg_1" =
  test_regex
    (CharacterClass (InvertedCC (RangeCR (sc 'a', sc 'c', EmptyCR))))
    "bbbb"
    0 ();
  [%expect {| No match on 'bbbb' |}]

let%expect_test "negated_char_class_seq_0_neg_2" =
  test_regex
    (CharacterClass (InvertedCC (RangeCR (sc 'a', sc 'c', EmptyCR))))
    "cbbb"
    0 ();
  [%expect {| No match on 'cbbb' |}]

let%expect_test "negated_char_class_seq_0_pos_0" =
  test_regex
    (CharacterClass (InvertedCC (RangeCR (sc 'a', sc 'c', EmptyCR))))
    " bbb"
    0 ();
  [%expect {| Matched 1 characters ([0-1]) in ' bbb' (length=4) |}]

let%expect_test "negated_char_class_seq_0_pos_1" =
  test_regex
    (CharacterClass (InvertedCC (RangeCR (sc 'a', sc 'c', EmptyCR))))
    "dbbb"
    0 ();
  [%expect {|Matched 1 characters ([0-1]) in 'dbbb' (length=4) |}]





let%expect_test "sequence" =
  test_regex
    ((cchar 'a') -- (cchar 'b') -- (cchar 'b'))
    "abbb"
    0 ();
  [%expect {| Matched 3 characters ([0-3]) in 'abbb' (length=4) |}]


let%expect_test "greedy_star" = 
  test_regex
    (!* (cchar 'a'))
    "aaaaa"
    0 ();
  [%expect {| Matched 5 characters ([0-5]) in 'aaaaa' (length=5) |}]


let%expect_test "lazy_star_0" = 
  test_regex
    (!*? (cchar 'a'))
    "aaaaa"
    0 ();
  [%expect {| Matched 0 characters ([0-0]) in 'aaaaa' (length=5) |}]

let%expect_test "lazy_star_1" = 
  test_regex
    (!*? (cchar 'a') -- (cchar 'b'))
    "aaaaab"
    0 ();
  [%expect {| Matched 6 characters ([0-6]) in 'aaaaab' (length=6) |}]

let%expect_test "groups" =
  test_regex
    (   group ( cchar 'a')
    ||  group ( cchar 'b'))
    "ab"
    0 ();
  [%expect {|
    Matched 1 characters ([0-1]) in 'ab' (length=2)
    Group 1: 'a' ([0-1])
    Group 2: undefined |}]


let%expect_test "capture_reset" =
  test_regex
    !*( group (cchar 'a')
    ||  group (cchar 'b'))
    "ab"
    0 ();
  [%expect {|
    Matched 2 characters ([0-2]) in 'ab' (length=2)
    Group 1: undefined
    Group 2: 'b' ([1-2]) |}]




let%expect_test "case_insensitive_0_pos_0" =
  test_regex
    (CharacterClass (NoninvertedCC (ClassAtomCR (sc 'a', EmptyCR))))
    "abbb"
    0 ~ignoreCase:true ();
  [%expect {| Matched 1 characters ([0-1]) in 'abbb' (length=4) |}]

let%expect_test "case_insensitive_0_pos_1" =
  test_regex
    (CharacterClass (NoninvertedCC (ClassAtomCR (sc 'a', EmptyCR))))
    "Abbb"
    0 ~ignoreCase:true ();
  [%expect {| Matched 1 characters ([0-1]) in 'Abbb' (length=4) |}]

let%expect_test "case_insensitive_0_pos_2" =
  test_regex
    (CharacterClass (NoninvertedCC (ClassAtomCR (sc 'A', EmptyCR))))
    "abbb"
    0 ~ignoreCase:true ();
  [%expect {| Matched 1 characters ([0-1]) in 'abbb' (length=4) |}]

let%expect_test "case_insensitive_0_pos_3" =
  test_regex
    (CharacterClass (NoninvertedCC (ClassAtomCR (sc 'A', EmptyCR))))
    "Abbb"
    0 ~ignoreCase:true ();
  [%expect {| Matched 1 characters ([0-1]) in 'Abbb' (length=4) |}]


let%expect_test "case_insensitive_0_neg_0" =
  test_regex
    (CharacterClass (NoninvertedCC (ClassAtomCR (sc 'a', EmptyCR))))
    "bbbb"
    0 ~ignoreCase:true ();
  [%expect {| No match on 'bbbb' |}]

let%expect_test "case_insensitive_0_neg_1" =
  test_regex
    (CharacterClass (NoninvertedCC (ClassAtomCR (sc 'a', EmptyCR))))
    "Bbbb"
    0 ~ignoreCase:true ();
  [%expect {| No match on 'Bbbb' |}]



let%expect_test "hex_escape_0" =
  test_regex
    (AtomEsc (ACharacterEsc (HexEscape ('6', '1'))))
    "a"
    0 ();
  [%expect {| Matched 1 characters ([0-1]) in 'a' (length=1) |}]

let%expect_test "hex_escape_1" =
  test_regex
    (AtomEsc (ACharacterEsc (HexEscape ('7', 'c'))))
    "|"
    0 ();
  [%expect {| Matched 1 characters ([0-1]) in '|' (length=1) |}]

let%expect_test "hex_escape_2" =
  test_regex
    (AtomEsc (ACharacterEsc (HexEscape ('7', 'c'))))
    "a"
    0 ();
  [%expect {| No match on 'a' |}]



let%expect_test "c_escape_0" =
  test_regex
    (AtomEsc (ACharacterEsc (AsciiControlEsc ('i'))))
    "\t"
    0 ();
  [%expect {| Matched 1 characters ([0-1]) in '	' (length=1) |}]

let%expect_test "c_escape_1" =
  test_regex
    (AtomEsc (ACharacterEsc (AsciiControlEsc ('I'))))
    "\t"
    0 ();
  [%expect {| Matched 1 characters ([0-1]) in '	' (length=1) |}]

let%expect_test "c_escape_2" =
  test_regex
    (AtomEsc (ACharacterEsc (AsciiControlEsc ('i'))))
    "a"
    0 ();
  [%expect {| No match on 'a' |}]


let%expect_test "dot_greek" =
  test_regex
    (!* Dot)
    "αβγδεϝͷϛζͱηθιϳκλμνξοπϻϟϙρσͼτυφχψωϡͳϸ"
    0 ();
  [%expect {| Matched 36 characters ([0-36]) in 'αβγδεϝͷϛζͱηθιϳκλμνξοπϻϟϙρσͼτυφχψωϡͳϸ' (length=36) |}]