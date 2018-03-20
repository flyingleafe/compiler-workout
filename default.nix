with import <nixpkgs> {}; {
  ocamlEnv = pkgsi686Linux.stdenv.mkDerivation {
    name = "ocamlEnv";
    buildInputs = [
      ocaml
      opam
      m4
      ncurses
    ];
  };
}
