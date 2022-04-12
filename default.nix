{ z3
, mlcrypto
, lib
, stdenv
, fetchFromGitHub
, ocamlPackages
, git
, which
}:

stdenv.mkDerivation rec {
  name = "fstar";

  src = ./.;

  strictDeps = true;

  prePatch = ''
    git init

    git config user.name "Jane Doe"
    git config user.email "jane.doe@example.com"

    git add .
    export GIT_COMMITTER_DATE="1970-01-01T00:00:00"
    export GIT_AUTHOR_DATE="1970-01-01T00:00:00"
    git commit -m "first commit"
  '';

  postPatch = ''
    patchShebangs ulib/gen_mllib.sh
  '';

  nativeBuildInputs = [
    git
    which
    z3
  ] ++ (with ocamlPackages; [
    ocaml
    findlib
    ocamlbuild
    menhir
  ]);

  buildInputs = [
  ] ++ (with ocamlPackages; [
    batteries
    zarith
    stdint
    yojson
    fileutils
    menhirLib
    pprint
    sedlex_2
    ppxlib
    ppx_deriving
    ppx_deriving_yojson
    process
  ]);

  makeFlags = [ "PREFIX=$(out)" ];

  enableParallelBuilding = true;

  installPhase = ''
    export Z3_LICENSE=${z3.license}
    make package
    cp -r ./src/ocaml-output/fstar $out
  '';
}
