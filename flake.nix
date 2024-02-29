{
  description = "A mechanization of the ECMAScript specification of regexes.";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/3cb4ae6689d2aa3f363516234572613b31212b78";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }@input: 
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; };
      in {
        devShells = {
            default = pkgs.mkShell {
              buildInputs = with pkgs; [
                coq

                ocaml
                dune_3
                ocamlPackages.ocamlformat
                ocamlPackages.ocaml-lsp
                ocamlPackages.findlib
                ocamlPackages.ppx_expect
                ocamlPackages.menhir
                ocamlPackages.yojson
                ocamlPackages.integers
                ocamlPackages.uucp
                ocamlPackages.ansiterminal

                nodejs_21
                node2nix
              ];
          };
        };
      });
}
