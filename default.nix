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
      mathpartir
      standalone;
  };
in
  pkgs.stdenv.mkDerivation rec {
    name = "agda-synthetic-categories";

    src = pkgs.nix-gitignore.gitignoreSource [] ./.;

    buildInputs = [
      af
      tex
    ];

    buildPhase = ''
      mkdir -p trees/stt/autogen
      bash ./scripts/generateEverything.sh
      echo "Generated everything file"
      mkdir -p ./output
      mkdir -p ./output/html
      echo "made /output/html dir"
      LC_ALL=C.UTF-8 Agda_datadir=./_build agda-forester --forest -otrees/stt/autogen --fhtml-dir=output/html src/Everything.agda
      echo "Generated trees"
      forester build --no-theme
      if [ -f ./output/agda-synthetic-categories/Agda.css ]; then
        if ! cp ./output/agda-synthetic-categories/Agda.css ./output/html/Agda.css; then
          echo "Warning: failed to copy Agda.css into output/html; continuing." >&2
        fi
      else
        echo "Warning: ./output/agda-synthetic-categories/Agda.css not found; skipping copy." >&2
      fi
    '';

    installPhase = ''
      echo $out
      mkdir -p $out
      cp -Lrvf output/agda-synthetic-categories/* "$out"/
      cp -Lrvf output/html "$out"/
    '';
  }
