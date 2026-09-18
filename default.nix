{
  system ? builtins.currentSystem,
}:
let
  thunkSource = (import ./nix/nix-thunk { }).thunkSource;
  # pkgs = import <nixpkgs> { inherit system; };
  pkgs = import "${thunkSource ./nix/agda-forester}/nix/nixpkgs.nix" { inherit system; };

  af = import ./nix/agda-forester { };

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
      standalone
      bbold
      bbold-type1
      ;
  };
in
pkgs.stdenv.mkDerivation rec {
  name = "agda-synthetic-categories";

  src = pkgs.nix-gitignore.gitignoreSource [ ] ./.;

  buildInputs = [
    af
    tex
  ];

  buildPhase = ''
    LC_ALL=C.UTF-8 make nix-build
  '';

  installPhase = ''
    echo $out
    mkdir -p $out
    cp -Lrvf output/agda-synthetic-categories/* "$out"/
    cp -Lrvf output/html "$out"/
    mkdir -p "$out/assets"
    cp -Lrvf assets/logo-wide-transparent.svg "$out/assets"/
    cp -Lrvf assets/ML_workshop_photo.JPG "$out/assets"/
    mkdir -p "$out/benchmarks"
    cp -Lrvf assets/benchmarks/. "$out/benchmarks"/
    if [ -f "$out/benchmarks/data.json" ]; then
      printf 'window.BENCHMARK_DATA = ' > "$out/benchmarks/data.js"
      cat "$out/benchmarks/data.json" >> "$out/benchmarks/data.js"
    fi
  '';
}
