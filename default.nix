{ system ? builtins.currentSystem }:
let
  thunkSource = (import ./nix/nix-thunk {}).thunkSource;
  # pkgs = import <nixpkgs> { inherit system; };
  pkgs = import "${thunkSource ./nix/agda-forester}/nix/nixpkgs.nix"
                 { inherit system; };

  af = import ./nix/agda-forester {};

  tex = pkgs.texlive.combine {
    inherit (pkgs.texlive)
      collection-basic
      collection-latex
      pgf
      tikz-cd
      quiver
      babel
      mathtools
      dvisvgm
      standalone;
  };
in
  pkgs.stdenv.mkDerivation rec {
    name = "synthetic-agda";

    src = pkgs.nix-gitignore.gitignoreSource [] ./.;

    buildInputs = [
      af
      af.passthru.forest
      tex
    ];

    # shellHook = ''
    #   export out=site
    # '';


    buildPhase = ''
      ./generateEverything.sh
      echo "Generated everything file"
      agda-forester --forest -otrees/stt/autogen src/Everything.agda
      echo "Generated trees"
      forester build
    '';

    installPhase = ''
      echo $out
      mkdir -p $out
      cp -Lrvf output/* "$out"/
    '';
  }
