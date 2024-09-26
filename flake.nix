{
  description = "A mechanization of the specification of ECMAScript regexes.";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs";
    flake-utils.url = "github:numtide/flake-utils";
    # melange = {
    #   url = "github:melange-re/melange/4.0.0-414";
    #   inputs.nixpkgs.follows = "nixpkgs";
    #   inputs.flake-utils.follows = "flake-utils";
    # };

    ocaml-overlay = {
      url = "github:nix-ocaml/nix-overlays";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs = { self, nixpkgs, flake-utils, ocaml-overlay }@input: 
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; overlays = [ ocaml-overlay.overlays.default ]; };
      in {
        devShells = {
          default = pkgs.mkShell {
            buildInputs = (with pkgs; [
              # coq

              # coqPackages.serapi
              # python311Packages.alectryon

              nodejs_22
              nodePackages.webpack-cli
            ]) ++ (with pkgs.ocaml-ng.ocamlPackages_4_14; [
              ocaml
              dune_3
              # ocamlformat
              ocaml-lsp
              findlib
              integers
              # uucp
              ppx_expect
              # melange.packages."${system}".melange
              melange
              zarith
            ]);
          };
        };
      });
}
