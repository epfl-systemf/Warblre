(lang dune 3.23)

(name warblre)

(generate_opam_files true)

(using rocq 0.13)
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
  (rocq-stdlib (>= 9.0.0))
  (rocq-core (>= 9.0.0))))

(package
 (name warblre-engines)
 (synopsis "Regex engines extracted from Warblre")
 (depends
  (ocaml (= 4.14.2))
  (warblre (= :version))
  (integers (>= 0.7.0))
  (uucp (>= 15.0.0))
  (zarith (>= 1.13))
  (melange (= 5.1.0-414))
  (ppx_expect (>= v0.16.0))))
