let
  pkgs = import <nixpkgs> {};
  fstars = pkgs.fstars;
  factory = fstars.factory;
  fstar = fstars.master-unicode-op;
  buildInputs = fstar.buildInputs ++ [
    (pkgs.writeScriptBin "generate-ocaml"
      ''cd ${toString ./.}
        make -C src ocaml''
    )
    (pkgs.writeScriptBin "build-ocaml"
      ''cd ${toString ./.}
        rm ./bin/fstar.exe
        make -C src/ocaml-output ../../bin/fstar.exe''
    )
  ];
in

pkgs.mkShell {
  name = "dev-env-fstar-compiler";
  inherit buildInputs;

  shellHook = ''
     (
       cd ${toString ./.}
       bash fstar-missing-files/copy.sh || true
       ln -s ${fstar}/bin/fstar.exe ./bin/fstar.exe
     )
  '';
}

