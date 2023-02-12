{ fstar, fstar-dune, fstar-ocaml-snapshot, stdenv, ulib }:

let
  dune-src = stdenv.mkDerivation {
    name = "src";
    src = fstar-ocaml-snapshot;
    dontBuild = true;
    installPhase = ''
      mkdir -p $out/ocaml
      cp -r ./* $out/ocaml
      cp ${../version.txt} $out
    '';
  };
  fstar-dune-bootstrap = fstar-dune.overrideAttrs (_: { src = dune-src; });
  ulib-bootstrap = ulib.override (_: { fstar-dune = fstar-dune-bootstrap; });

in fstar.override (_: {
  fstar-dune = fstar-dune-bootstrap;
  ulib = ulib-bootstrap;
})
