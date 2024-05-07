{
  description = "A mechanization of the specification of ECMAScript regexes.";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixos-23.11";
    flake-utils.url = "github:numtide/flake-utils";
    melange = {
      url = "github:melange-re/melange/v3-414";
      inputs.nixpkgs.follows = "nixpkgs";
      inputs.flake-utils.follows = "flake-utils";
    };
  };

  outputs = { self, nixpkgs, flake-utils, melange }@input: 
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; overlays = [ melange.overlays.default ]; };
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
                ocamlPackages.melange

                nodejs_21
                nodePackages.webpack-cli
              ];
          };
        };
      });
}
