open Warblre.OCamlEngines.UnicodeNotations
open Warblre.OCamlEngines.UnicodeTester

let%expect_test "char_class_atom_0_pos" =
  test_regex
    (CharacterClass (NoninvertedCC (ClassAtomCR (sc 'a', EmptyCR))))
    "abbb"
    0 ();
  [%expect {|
    Regex /[a]/ on 'abbb' at 0:
    Input: abbb
    End: 1
    Captures:
    	None |}]

let%expect_test "char_class_atom_0_neg" =
  test_regex
    (CharacterClass (NoninvertedCC (ClassAtomCR (sc 'b', EmptyCR))))
    "abbb"
    0 ();
  [%expect {|
    Regex /[b]/ on 'abbb' at 0:
    No match |}]

let%expect_test "negated_char_class_atom_0_pos" =
  test_regex
    (CharacterClass (InvertedCC (ClassAtomCR (sc 'b', EmptyCR))))
    "abbb"
    0 ();
  [%expect {|
    Regex /[^b]/ on 'abbb' at 0:
    Input: abbb
    End: 1
    Captures:
    	None |}]

let%expect_test "negated_char_class_atom_0_neg" =
  test_regex
    (CharacterClass (InvertedCC (ClassAtomCR (sc 'a', EmptyCR))))
    "abbb"
    0 ();
  [%expect {|
    Regex /[^a]/ on 'abbb' at 0:
    No match |}]




let%expect_test "char_class_seq_0_pos_0" =
  test_regex
    (CharacterClass (NoninvertedCC (RangeCR (sc 'a', sc 'c', EmptyCR))))
    "abbb"
    0 ();
  [%expect {|
    Regex /[a-c]/ on 'abbb' at 0:
    Input: abbb
    End: 1
    Captures:
    	None |}]

let%expect_test "char_class_seq_0_pos_1" =
  test_regex
    (CharacterClass (NoninvertedCC (RangeCR (sc 'a', sc 'c', EmptyCR))))
    "bbbb"
    0 ();
  [%expect {|
    Regex /[a-c]/ on 'bbbb' at 0:
    Input: bbbb
    End: 1
    Captures:
    	None |}]

let%expect_test "char_class_seq_0_pos_2" =
  test_regex
    (CharacterClass (NoninvertedCC (RangeCR (sc 'a', sc 'c', EmptyCR))))
    "cbbb"
    0 ();
  [%expect {|
    Regex /[a-c]/ on 'cbbb' at 0:
    Input: cbbb
    End: 1
    Captures:
    	None |}]

let%expect_test "char_class_seq_0_neg_0" =
  test_regex
    (CharacterClass (NoninvertedCC (RangeCR (sc 'a', sc 'c', EmptyCR))))
    " bbb"
    0 ();
  [%expect {|
    Regex /[a-c]/ on ' bbb' at 0:
    No match |}]

let%expect_test "char_class_seq_0_neg_1" =
  test_regex
    (CharacterClass (NoninvertedCC (RangeCR (sc 'a', sc 'c', EmptyCR))))
    "dbbb"
    0 ();
  [%expect {|
    Regex /[a-c]/ on 'dbbb' at 0:
    No match |}]





let%expect_test "negated_char_class_seq_0_neg_0" =
  test_regex
    (CharacterClass (InvertedCC (RangeCR (sc 'a', sc 'c', EmptyCR))))
    "abbb"
    0 ();
  [%expect {|
    Regex /[^a-c]/ on 'abbb' at 0:
    No match |}]

let%expect_test "negated_char_class_seq_0_neg_1" =
  test_regex
    (CharacterClass (InvertedCC (RangeCR (sc 'a', sc 'c', EmptyCR))))
    "bbbb"
    0 ();
  [%expect {|
    Regex /[^a-c]/ on 'bbbb' at 0:
    No match |}]

let%expect_test "negated_char_class_seq_0_neg_2" =
  test_regex
    (CharacterClass (InvertedCC (RangeCR (sc 'a', sc 'c', EmptyCR))))
    "cbbb"
    0 ();
  [%expect {|
    Regex /[^a-c]/ on 'cbbb' at 0:
    No match |}]

let%expect_test "negated_char_class_seq_0_pos_0" =
  test_regex
    (CharacterClass (InvertedCC (RangeCR (sc 'a', sc 'c', EmptyCR))))
    " bbb"
    0 ();
  [%expect {|
    Regex /[^a-c]/ on ' bbb' at 0:
    Input:  bbb
    End: 1
    Captures:
    	None |}]

let%expect_test "negated_char_class_seq_0_pos_1" =
  test_regex
    (CharacterClass (InvertedCC (RangeCR (sc 'a', sc 'c', EmptyCR))))
    "dbbb"
    0 ();
  [%expect {|
    Regex /[^a-c]/ on 'dbbb' at 0:
    Input: dbbb
    End: 1
    Captures:
    	None |}]





let%expect_test "sequence" =
  test_regex
    ((cchar 'a') -- (cchar 'b') -- (cchar 'b'))
    "abbb"
    0 ();
  [%expect {|
    Regex /abb/ on 'abbb' at 0:
    Input: abbb
    End: 3
    Captures:
    	None |}]


let%expect_test "greedy_star" = 
  test_regex
    (!* (cchar 'a'))
    "aaaaa"
    0 ();
  [%expect {|
    Regex /a*/ on 'aaaaa' at 0:
    Input: aaaaa
    End: 5
    Captures:
    	None |}]


let%expect_test "lazy_star_0" = 
  test_regex
    (!*? (cchar 'a'))
    "aaaaa"
    0 ();
  [%expect {|
    Regex /a*?/ on 'aaaaa' at 0:
    Input: aaaaa
    End: 0
    Captures:
    	None |}]

let%expect_test "lazy_star_1" = 
  test_regex
    (!*? (cchar 'a') -- (cchar 'b'))
    "aaaaab"
    0 ();
  [%expect {|
    Regex /a*?b/ on 'aaaaab' at 0:
    Input: aaaaab
    End: 6
    Captures:
    	None |}]

let%expect_test "groups" =
  test_regex
    (   group ( cchar 'a')
    ||  group ( cchar 'b'))
    "ab"
    0 ();
  [%expect {|
    Regex /(a)|(b)/ on 'ab' at 0:
    Input: ab
    End: 1
    Captures:
    	# 0 : (0,1)
    	# 1 : Undefined |}]


let%expect_test "capture_reset" =
  test_regex
    !*( group (cchar 'a')
    ||  group (cchar 'b'))
    "ab"
    0 ();
  [%expect {|
    Regex /(?:(a)|(b))*/ on 'ab' at 0:
    Input: ab
    End: 2
    Captures:
    	# 0 : Undefined
    	# 1 : (1,2) |}]




let%expect_test "case_insensitive_0_pos_0" =
  test_regex
    (CharacterClass (NoninvertedCC (ClassAtomCR (sc 'a', EmptyCR))))
    "abbb"
    0 ~ignoreCase:true ();
  [%expect {|
    Regex /[a]/ on 'abbb' at 0:
    Input: abbb
    End: 1
    Captures:
    	None |}]

let%expect_test "case_insensitive_0_pos_1" =
  test_regex
    (CharacterClass (NoninvertedCC (ClassAtomCR (sc 'a', EmptyCR))))
    "Abbb"
    0 ~ignoreCase:true ();
  [%expect {|
    Regex /[a]/ on 'Abbb' at 0:
    Input: Abbb
    End: 1
    Captures:
    	None |}]

let%expect_test "case_insensitive_0_pos_2" =
  test_regex
    (CharacterClass (NoninvertedCC (ClassAtomCR (sc 'A', EmptyCR))))
    "abbb"
    0 ~ignoreCase:true ();
  [%expect {|
    Regex /[A]/ on 'abbb' at 0:
    Input: abbb
    End: 1
    Captures:
    	None |}]

let%expect_test "case_insensitive_0_pos_3" =
  test_regex
    (CharacterClass (NoninvertedCC (ClassAtomCR (sc 'A', EmptyCR))))
    "Abbb"
    0 ~ignoreCase:true ();
  [%expect {|
    Regex /[A]/ on 'Abbb' at 0:
    Input: Abbb
    End: 1
    Captures:
    	None |}]


let%expect_test "case_insensitive_0_neg_0" =
  test_regex
    (CharacterClass (NoninvertedCC (ClassAtomCR (sc 'a', EmptyCR))))
    "bbbb"
    0 ~ignoreCase:true ();
  [%expect {|
    Regex /[a]/ on 'bbbb' at 0:
    No match |}]

let%expect_test "case_insensitive_0_neg_1" =
  test_regex
    (CharacterClass (NoninvertedCC (ClassAtomCR (sc 'a', EmptyCR))))
    "Bbbb"
    0 ~ignoreCase:true ();
  [%expect {|
    Regex /[a]/ on 'Bbbb' at 0:
    No match |}]



let%expect_test "hex_escape_0" =
  test_regex
    (AtomEsc (ACharacterEsc (hex_escape '6' '1')))
    "a"
    0 ();
  [%expect{|
    Regex /\x61/ on 'a' at 0:
    Input: a
    End: 1
    Captures:
    	None |}]

let%expect_test "hex_escape_1" =
  test_regex
    (AtomEsc (ACharacterEsc (hex_escape '7' 'c')))
    "|"
    0 ();
  [%expect{|
    Regex /\x7C/ on '|' at 0:
    Input: |
    End: 1
    Captures:
    	None |}]

let%expect_test "hex_escape_2" =
  test_regex
    (AtomEsc (ACharacterEsc (hex_escape '7' 'c')))
    "a"
    0 ();
  [%expect{|
    Regex /\x7C/ on 'a' at 0:
    No match |}]



let%expect_test "c_escape_0" =
  test_regex
    (AtomEsc (ACharacterEsc (AsciiControlEsc ('i'))))
    "\t"
    0 ();
  [%expect{|
    Regex /\ci/ on '	' at 0:
    Input:
    End: 1
    Captures:
    	None |}]

let%expect_test "c_escape_1" =
  test_regex
    (AtomEsc (ACharacterEsc (AsciiControlEsc ('I'))))
    "\t"
    0 ();
  [%expect{|
    Regex /\cI/ on '	' at 0:
    Input:
    End: 1
    Captures:
    	None |}]

let%expect_test "c_escape_2" =
  test_regex
    (AtomEsc (ACharacterEsc (AsciiControlEsc ('i'))))
    "a"
    0 ();
  [%expect{|
    Regex /\ci/ on 'a' at 0:
    No match |}]


let%expect_test "dot_greek" =
  test_regex
    (!* Dot)
    "αβγδεϝͷϛζͱηθιϳκλμνξοπϻϟϙρσͼτυφχψωϡͳϸ"
    0 ();
  [%expect {|
    Regex /.*/ on 'αβγδεϝͷϛζͱηθιϳκλμνξοπϻϟϙρσͼτυφχψωϡͳϸ' at 0:
    Input: αβγδεϝͷϛζͱηθιϳκλμνξοπϻϟϙρσͼτυφχψωϡͳϸ
    End: 36
    Captures:
    	None |}]