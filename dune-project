(lang dune 3.8)

(name warblre)

(generate_opam_files true)

(using coq 0.8)

(authors "Noé De Santo" "Aurèle Barrière" "Clément Pit-Claudel")

(maintainers "Noé De Santo" "Aurèle Barrière")

(package
 (name warblre)
 (synopsis "A mechanization of the specification of ECMAScript regexes.")
 (depends ocaml dune coq js_of_ocaml js_of_ocaml-ppx integers_stubs_js integers uucp ppx_expect))