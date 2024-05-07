(lang dune 3.8)

(name warblre)

(generate_opam_files true)

(using coq 0.8)
(using melange 0.1)

(authors "Noé De Santo" "Aurèle Barrière" "Clément Pit-Claudel")

(maintainers "Noé De Santo" "Aurèle Barrière")

(package
 (name warblre)
 (synopsis "A mechanization of the specification of ECMAScript regexes.")
 (depends ocaml dune coq integers uucp melange ppx_expect))
