{
system ? builtins.currentSystem
}:
let
  pkgs = import <nixpkgs> { inherit system; };
  af = (import ./nix/agda-forester { inherit system; });
  drv = (import ./default.nix { inherit system; });
  forester-server = builtins.getFlake "github:kentookura/forest-server?rev=d33690f372ae0ba87df48b59b5deb7148752839b";
in pkgs.mkShell {
    name = "agda-forester-shell";

    buildInputs = [
      (forester-server.packages.${system}.default)
      (pkgs.python3.withPackages (py-pkgs: []))
      (pkgs.codespell)
    ] ++ drv.buildInputs;

    shellHook = ''
    echo "Welcome to the dev shell!"
    echo "Agda version: $(agda --version)"
    echo "Forester version: $(forester --version || echo not found)"
    '';
}
