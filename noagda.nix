{
system ? builtins.currentSystem
}:
let
  pkgs = import <nixpkgs> { inherit system; };

  forester = builtins.getFlake "sourcehut:~jonsterling/ocaml-forester?tag=5.0";

  myForester = forester.legacyPackages.${system};

  overlay = final: prev: {
    dune = prev.dune.overrideAttrs (o: {
      version = "3.17.2";
      src = builtins.fetchurl {
        url = "https://github.com/ocaml/dune/releases/download/3.17.2/dune-3.17.2.tbz";
        sha256 = "0r7al83jwkdfk6qvb53vrlzzfr08gwcydn1ccigfdsfg1vnzxslx";
      };
      nativeBuildInputs = o.nativeBuildInputs ++ [ pkgs.makeWrapper ];
      postFixup =
        if pkgs.stdenv.isDarwin then ''
           wrapProgram $out/bin/dune \
           --suffix PATH : "${pkgs.darwin.sigtool}/bin"
        '' else "";
    });

    forester = prev.forester.overrideAttrs (_: {
      DUNE_CACHE = "enabled";
      DUNE_CACHE_TRANSPORT = "direct";
      XDG_CACHE_HOME = "/tmp/dune-cache";
    });
  };
  myForester' = myForester.overrideScope overlay;

  forester-server = builtins.getFlake "github:kentookura/forest-server?rev=d33690f372ae0ba87df48b59b5deb7148752839b";
in pkgs.mkShell {
    name = "agda-forester-shell";

    buildInputs = [
      (forester-server.packages.${system}.default)
      (myForester'.forester)
      (pkgs.python3.withPackages (py-pkgs: []))
      (pkgs.codespell)
      (pkgs.ripgrep)
    ];

    shellHook = ''
    echo "Welcome to the lightweight dev shell!"
    echo "Forester version: $(forester --version || echo not found)"
    '';
}
