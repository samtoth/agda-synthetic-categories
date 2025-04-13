{
system ? builtins.currentSystem
}:
let
  pkgs = import <nixpkgs> { inherit system; };
  af = (import ./nix/agda-forester { inherit system; });
  drv = (import ./default.nix { inherit system; });
in pkgs.mkShell {
    name = "agda-forester-shell";

    buildInputs = [
      af
      af.passthru.forest
    ];

    shellHook = ''
    echo "Welcome to the dev shell!"
    echo "Agda version: $(agda --version)"
    echo "Forester version: $(forester --version || echo not found)"
    '';
}