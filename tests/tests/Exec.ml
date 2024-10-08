let%expect_test "sequence" =
  Warblre.OCamlEngines.UnicodeTester.test_exec
    Warblre.OCamlEngines.UnicodeNotations.((cchar 'a') -- (cchar 'b') -- (cchar 'b'))
    "abbb";
  [%expect {|
    Regex /abb/ on 'abbb' at 0 (using exec):
    Start:[20G0
    Captures:[20G# 0[32G: 'abb'[64G |}]

let%expect_test "unicode_u" =
  Warblre.OCamlEngines.UnicodeTester.test_exec ~d:true
    Warblre.OCamlEngines.UnicodeNotations.(group !* (
      ngroup ("G", char "a") ||
      group (char "b") ||
      (char "π") ||
      (char "🧭")))
    "aaaaabaπaa🧭aaccaa";
  [%expect {|
    Regex /((?:(?<G>a)|(b)|π|🧭)*)/ on 'aaaaabaπaa🧭aaccaa' at 0 (using exec):
    Start:[20G0
    Captures:[20G# 0[32G: 'aaaaabaπaa🧭aa'[64G(0,14)
    [20G# 1[32G: 'aaaaabaπaa🧭aa'[64G(0,14)
    [20G# 2[32G: 'a'[64G(13,14)
    [20G# 3[32G: Undefined[64G
    Named captures:[20G# G[32G: 'a'[64G(13,14) |}]

let%expect_test "unicode_non_u" =
  Warblre.OCamlEngines.Utf16Tester.test_exec
    Warblre.OCamlEngines.Utf16Notations.(group !* (
        ngroup ("G", char "a") ||
        group (char "b") ||
        (char "π")))
    "aaaaabaπaa🧭aaccaa";
  [%expect {|
    Regex /((?:(?<G>a)|(b)|π)*)/ on 'aaaaabaπaa🧭aaccaa' at 0 (using exec):
    Start:[20G0
    Captures:[20G# 0[32G: 'aaaaabaπaa'[64G
    [20G# 1[32G: 'aaaaabaπaa'[64G
    [20G# 2[32G: 'a'[64G
    [20G# 3[32G: Undefined[64G
    Named captures:[20G# G[32G: 'a'[64G |}]