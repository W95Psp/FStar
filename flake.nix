{
  description = "F* flake";

  inputs = {
    flake-utils.url = "github:numtide/flake-utils";
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-20.09";
    fstar-flake.url = "github:W95Psp/nix-flake-fstar";
  };
  
  outputs = { self, nixpkgs, flake-utils, fstar-flake }:
    flake-utils.lib.eachSystem [ "x86_64-darwin" "x86_64-linux"]
      (system:
        let
          pkgs = nixpkgs.legacyPackages.${system};
          fstar = fstar-flake.defaultPackage.${system};
          lib = pkgs.lib;
        in  
          rec {
            packages = {
              fstar = fstar.override ({ name = "fstar-dev";
                                        src = pkgs.lib.cleanSource ./.;
                                      });
            };
            defaultPackage = packages.fstar;
            devShell = pkgs.mkShell {
              name = "dev-env-fstar-compiler";
              buildInputs = fstar.buildInputs ++ [
                fstar
                (pkgs.writeScriptBin "cp-fstar"
                  ''cp  --no-preserve=all ${fstar}/bin/fstar.exe ./bin/fstar.exe
                    chmod +x ./bin/fstar.exe
                  ''
                )
                (pkgs.writeScriptBin "clear_ranges"
                  ''#! /usr/bin/env sh
                    for file in "$@"; do
                        # Clear ranges
                        ${pkgs.sd}/bin/sd '\s*FStar_Range.line\s*=\s*\d+\s*;\s*col\s*=\s*\d+\s*'       ""   "$file"
                        ${pkgs.sd}/bin/sd '\s*(start|end)_pos\s*=\s*\{\s*\}\s*;?\s*'                   ""   "$file"
                        ${pkgs.sd}/bin/sd '\s*\{\s*FStar_Range.file_name\s*=\s*"[^"]+"\s*;\s*\}\s*'    ""   "$file"
                        ${pkgs.sd}/bin/sd '\s*\{(FStar_Range\.def_range|use_range|[\s=;]+)*\}\s*'      "{}" "$file"
                        
                        # Clear "Prims"
                        ${pkgs.sd}/bin/sd '\s*\{\s*FStar_Ident\.idText\s*=\s*"Prims"\s*;\s*idRange\s*=\s*\{\s*\}\s*\}\s*' "" "$file"
                        ${pkgs.sd}/bin/sd '=\s*\[\s*\]\s*;' '= [];' "$file"
                        ${pkgs.sd}/bin/sd 'Prims\.?' "" "$file"
                        # ${pkgs.sd}/bin/sd '"Prims\.([^"]+)"' '"$1"' "$file"
                        # ${pkgs.sd}/bin/sd 'nsstr\s+=\s+"Prims"' 'nsstr = ""' "$file"

                        echo "'$file' patched"
                    done
                  ''
                )
                (pkgs.writeScriptBin "generate-ocaml"
                  ''make ocaml -C src -j6''
                )
                (pkgs.writeScriptBin "build-ocaml"
                  ''{rm ./bin/fstar.exe.old || true} &> /dev/null
                    mv ./bin/fstar.exe ./bin/fstar.exe.old
                    if make -C src/ocaml-output ../../bin/fstar.exe; then
                       rm ./bin/fstar.exe.old;
                    else
                      mv ./bin/fstar.exe.old ./bin/fstar.exe
                    fi
                  ''
                )
              ];

              shellHook = ''bash fstar-missing-files/copy.sh || true
                            rm ./bin/fstar.exe || true
                            cp  --no-preserve=all ${fstar}/bin/fstar.exe ./bin/fstar.exe
                            chmod +x ./bin/fstar.exe
                         '';
            };
          }
      );
}
