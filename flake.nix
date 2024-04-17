{
  outputs = inputs: let
    EVPL = import inputs.self {system = "x86_64-linux";};
  in {
    packages.x86_64-linux.default = EVPL;
    overlays.default = final: prev: {
      agdaPackages = prev.agdaPackages.overrideScope' (self: super: {
        inherit EVPL;
      });
    };
  };
}
