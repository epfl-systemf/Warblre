(lang dune 3.14)

(name warblre)

(generate_opam_files true)

(using coq 0.8)
(using melange 0.1)
(using directory-targets 0.1)

(homepage "https://github.com/epfl-systemf/warblre")
(authors "Noé De Santo" "Aurèle Barrière" "Clément Pit-Claudel")
(maintainers "Noé De Santo" "Aurèle Barrière")
(bug_reports "https://github.com/epfl-systemf/warblre/issues")
(license BSD-3-Clause)

(package
 (name warblre)
 (synopsis "A mechanization of the specification of ECMAScript regexes")
 (depends
  (ocaml (= 4.14.2))))

(package
 (name warblre-engines)
 (synopsis "Regex engines extracted from Warblre")
 (depends
  (warblre (= :version))
  (integers (>= 0.7.0))
  (uucp (>= 15.0.0))
  (zarith (>= 1.13))
  (melange (= 3.0.0-414))
  (ppx_expect (>= v0.16.0))))