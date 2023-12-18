{ pkgs ? import <nixpkgs> {} }:
pkgs.mkShell
{
  buildInputs = with pkgs; [
    ocaml
    dune_3
    ocamlPackages.findlib
    ocamlPackages.ppx_assert
    ocamlPackages.ppx_expect
  ];
}
