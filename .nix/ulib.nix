{
  fstar-dune,
  lib,
  stdenv,
  version,
  z3,
  admit_queries ? false,
}:
stdenv.mkDerivation {
  pname = "fstar-ulib";
  inherit version;

  src = lib.sourceByRegex ./.. [
    "ulib.*"
    ".common.mk"
  ];

  nativeBuildInputs = [ z3 ];

  postPatch = ''
    mkdir -p bin
    cp ${fstar-dune}/bin/fstar.exe bin
    patchShebangs ulib/install-ulib.sh
    cd ulib
  '';

  makeFlags = [ "PREFIX=$(out)" ] ++ (if admit_queries then [ "ADMIT=1" ] else [ ]);

  enableParallelBuilding = true;
}
