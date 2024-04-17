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
pkgs.agdaPackages.mkDerivation {
  version = "1.0";
  pname = "EPVL";
  src = with pkgs.lib.fileset;
    toSource {
      root = ./.;
      fileset = gitTracked ./.;
    };

  buildInputs = [
    pkgs.agdaPackages.standard-library
  ];

  buildPhase = ''
    patchShebangs ./scripts/check-all.sh
    make check-all
    make build
  '';

  postInstall = ''
    install -D src/Main "$out/bin/$pname"
  '';

  meta = {description = "On the Expressive Power of Languages for Static Variability";};
}
