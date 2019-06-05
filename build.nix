let uu = import <nixpkgs> { }; in
{ stdenv ? uu.stdenv, fetchFromGitHub ? uu.fetchFromGitHub, makeWrapper ? uu.makeWrapper, ocamlPackages ? uu.ocamlPackages, z3 ? uu.z3 }:
stdenv.mkDerivation rec {
  name = "fstar-${version}";
  version = "3c80293f666fce21b9e794a36c59d53bd4873960";

  src = ./.;

  nativeBuildInputs = [ makeWrapper ];

  buildInputs = with ocamlPackages; [
    z3 ocaml findlib batteries menhir stdint zarith camlp4
    yojson pprint ulex ocaml-migrate-parsetree process
    ppx_deriving ppx_deriving_yojson ocamlbuild fileutils
    uu.file git uu.which
  ];

  makeFlags = [ "PREFIX=$(out)" ];

  # sed -i 's/\(launch_process : string ->\)/\1 list/g' ulib/FStar.Tactics.Builtins.fst
  preBuild = ''
    patchShebangs src/tools
    patchShebangs bin
  '';
  buildFlags = "-C src -j6 ocaml-fstar-ocaml"; # src/ocaml-output";

  preInstall = ''
    mkdir -p $out/lib/ocaml/${ocamlPackages.ocaml.version}/site-lib/fstarlib
  '';
  installFlags = "-C src/ocaml-output";
  postInstall = ''
    wrapProgram $out/bin/fstar.exe --prefix PATH ":" "${z3}/bin"
  '';

  meta = with stdenv.lib; {
    description = "ML-like functional programming language aimed at program verification";
    homepage = https://www.fstar-lang.org;
    license = licenses.asl20;
    platforms = with platforms; darwin ++ linux;
    maintainers = with maintainers; [ gebner ];
  };
}
