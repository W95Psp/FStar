/**
  Given an OCaml extraction of the F* compiler (via
   `fstar-ocaml-snapshot`), this derivation compiles a native
   `fstar.exe` binary and a checked `ulib`.
*/
{
  fstar,
  fstar-dune,
  fstar-ocaml-snapshot,
  fstar-ulib,
  stdenv,
  admit_queries,
  stage,
}:
let
  /** Compiles `fstar.exe` by bootstrapping `stage` times */
  bootstrap = stage:
    if stage <= 0
    then fstar-dune
    else
    let
      pname = "fstar-bootstrap-stage-${toString stage}";
      ocaml-src = stdenv.mkDerivation {
        name = "${pname}-src";
        src = fstar-ocaml-snapshot.override {
          inherit admit_queries;
          pname = "${pname}-ocaml";
          fstar = bootstrap (stage - 1);
        };
        dontBuild = true;
        installPhase = ''
          mkdir -p $out/ocaml
          mv ./* $out/ocaml
          cp ${../version.txt} $out/version.txt
        '';
      };
    in
      fstar-dune.overrideAttrs (_: {
        pname = "${pname}-dune";
        src = ocaml-src;
      });
  bootstrapped = bootstrap stage;
  fstar-ulib-bootstrap =
    (fstar-ulib.override (_: {
      inherit admit_queries;
      fstar-dune = bootstrapped;
    })).overrideAttrs
      (_: {
        pname = "fstar-ulib";
      });
in
fstar.override (_: {
  fstar-dune = bootstrapped;
  fstar-ulib = fstar-ulib-bootstrap;
})
