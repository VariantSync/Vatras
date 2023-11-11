{
  sources ? import ./nix/sources.nix,
  system ? builtins.currentSystem,
  pkgs ?
    import sources.nixpkgs {
      overlays = [];
      config = {};
      inherit system;
    },
}:
pkgs.agdaPackages.mkDerivation rec {
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
    make check-all
    make build
  '';

  installPhase = ''
    install -D src/Main "$out/bin/$pname"
  '';

  meta = {description = "On the Expressive Power of Programming Languages";};
}
