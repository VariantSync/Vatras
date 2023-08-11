# Goals
# Dependencies: agda-2.6.3, agda standard library at commit 177dc9e
# The standard library is part of this repository as a submodule in agda-stdlib.
# The submodule points at the standard library in the right version.
# To make it available while building and to editors, we have to set the AGDA_DIR
# environment variable to point to the "libs" directory in this repository
# export AGDA_DIR="path/to/this/repository/libs"
# I have documented more details on the setup in the README.md
{ pkgs ? import (fetchTarball "https://github.com/NixOS/nixpkgs/archive/refs/tags/23.05.tar.gz") {} }:
pkgs.agdaPackages.mkDerivation {
  version = "1.0";
  pname = "EPVL";
  src = ./.;

  buildInputs = [
    (pkgs.agdaPackages.standard-library.overrideAttrs
      (oldAttrs: {
        version = "1.7.2";
        src = pkgs.fetchFromGitHub {
          repo = "agda-stdlib";
          owner = "agda";
          rev = "177dc9e";
          hash = "sha256-ovnhL5otoaACpqHZnk/ucivwtEfBQtGRu4/xw4+Ws+c=";
        };
      }))
  ];

  buildPhase = ''
    make build
  '';

  installPhase = ''
    install -D src/Main "$out/bin/$pname"
  '';

  meta = { description = "On the Expressive Power of Programming Languages"; };
}
