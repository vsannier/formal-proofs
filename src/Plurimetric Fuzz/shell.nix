{ pkgs ? import <nixpkgs> {} }:

pkgs.mkShell {
  nativeBuildInputs = with pkgs; [
    coq
    coqPackages.stdlib
    coqPackages.autosubst
  ];
}
