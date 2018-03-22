with import <nixpkgs> {}; {
  ocamlEnv = pkgsi686Linux.stdenv.mkDerivation {
    name = "ocamlEnv";
    buildInputs = with pkgsi686Linux; [
      ocaml
      opam
      m4
    ];
  };
}
