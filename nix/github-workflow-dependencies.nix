{
  sources ? import ./sources.nix,
  system ? builtins.currentSystem,
  pkgs ?
    import sources.nixpkgs {
      overlays = [];
      config = {};
      inherit system;
    },
}: let
  Vatras = import ../default.nix {};
in
  pkgs.mkShell {
    inputsFrom = [Vatras];
  }
