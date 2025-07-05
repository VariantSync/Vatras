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
  version = "2.1";
  pname = "Vatras";
  src = with pkgs.lib.fileset;
    toSource {
      root = ./.;
      fileset = gitTracked ./.;
    };

  buildInputs = [
    pkgs.agdaPackages.standard-library
    pkgs.makeWrapper
  ];

  buildPhase = ''
    patchShebangs ./scripts/check-all.sh
    make check-all
    make build
  '';

  postInstall = ''
    install -D src/Main "$out/bin/$pname"
    wrapProgram "$out/bin/$pname" \
      --set LC_ALL C.UTF-8
  '';

  meta = {description = "On the Expressive Power of Languages for Static Variability";};
}
