/**
  Given a `fstar.exe` (via input `fstar`), this derivation runs F*
   to extract itself. As a result, this derivation produces one
   folder `ocaml` that contains a full extration of F*.
*/
{
  fstar,
  lib,
  ocamlPackages,
  stdenv,
  version,
  z3,
  pname ? "fstar-ocaml-snapshot",
  admit_queries ? false,
}:
stdenv.mkDerivation {
  inherit pname version;

  src = lib.cleanSourceWith {
    src = ./..;
    filter =
      path: _:
      let
        relPath = lib.removePrefix (toString ./.. + "/") (toString path);
      in
      lib.any (lib.flip lib.hasPrefix relPath) [
        "src"
        "ulib"
      ]
      || (
        lib.hasPrefix "ocaml" relPath
        && !(lib.hasInfix "/generated/" relPath)
        && !(lib.hasInfix "/dynamic/" relPath)
      )
      || lib.hasSuffix ".common.mk" relPath;
  };

  postPatch = ''
    mkdir -p bin
    cp ${fstar}/bin/fstar.exe bin
    cd src/ocaml-output
  '';

  nativeBuildInputs = with ocamlPackages; [
    ocaml
    menhir
    z3
  ];

  buildFlags = if admit_queries then [ "ADMIT=1" ] else [ ];

  installPhase = "mv ../../ocaml $out";

  enableParallelBuilding = true;
}
