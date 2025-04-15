{ system ? builtins.currentSystem }:
let
  pkgs = import <nixpkgs> { inherit system; };

  af = import ./nix/agda-forester {};
in
  pkgs.stdenv.mkDerivation rec {
    name = "synthetic-agda";

    src = ./.;
    
    buildInputs = [
      af
      af.passthru.forest
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