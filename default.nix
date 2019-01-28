{ pkgs ? (import <nixpkgs> {}), coq-version-or-url, bignums-url ? "", shell ? false }:

let
  coq-version-parts = builtins.match "([0-9]+).([0-9]+)" coq-version-or-url;
  coqPackages =
    if coq-version-parts == null then
      pkgs.mkCoqPackages (import (fetchTarball coq-version-or-url) {})
    else
      pkgs."coqPackages_${builtins.concatStringsSep "_" coq-version-parts}";
  bignums =
    if bignums-url == "" then coqPackages.bignums else
      coqPackages.bignums.overrideAttrs (o: {
        src = fetchTarball https://github.com/coq/bignums/archive/master.tar.gz;
      });
in

with coqPackages;

pkgs.stdenv.mkDerivation {

  name = "math-classes";

  propagatedBuildInputs = [
    coq
    bignums
  ];

  src = if shell then null else ./.;

  installFlags = "COQLIB=$(out)/lib/coq/${coq.coq-version}/";
}
