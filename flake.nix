{
  description = "A mechanization of the specification of ECMAScript regexes.";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixos-23.11";
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
                ocamlPackages.integers
                ocamlPackages.uucp
                ocamlPackages.ppx_expect

                nodejs_21
              ];
          };
        };
      });
}
