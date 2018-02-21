with import <nixpkgs> {}; {
  ocamlEnv = stdenv.mkDerivation {
    name = "ocamlEnv";
    buildInputs = [
      ocaml
      opam
      m4
      ncurses
    ];
  };
}
