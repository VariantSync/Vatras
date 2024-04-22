{
  outputs = inputs: {
    packages.x86_64-linux.default = import inputs.self {system = "x86_64-linux";};
    overlays.default = final: prev: {
      agdaPackages = prev.agdaPackages.overrideScope' (self: super: {
        (import inputs.self {
          system = "x86_64-linux";
          pkgs = final;
        };)
      });
    };
  };
}
