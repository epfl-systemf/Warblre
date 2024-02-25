{
  description = "A very basic flake";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/23.11";
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
                ocamlPackages.ppx_assert
                ocamlPackages.ppx_expect
                ocamlPackages.menhir
                ocamlPackages.yojson
                ocamlPackages.integers
                ocamlPackages.uutf
                ocamlPackages.uucp
                ocamlPackages.ansiterminal

                nodejs_21
                node2nix
              ];
          };
        };
      });
}
