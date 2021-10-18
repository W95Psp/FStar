{
  description = "F* flake";

  inputs = {
    flake-utils.url = "github:numtide/flake-utils";
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-21.05";
    fstar-flake.url = "github:W95Psp/nix-flake-fstar";
  };
  
  outputs = { self, nixpkgs, flake-utils, fstar-flake }:
    let
      dir_locals = ''
((fstar-mode
  (fstar-subp-sloppy . nil)
  (eval .
	(progn (defun my-fstar-compute-prover-args-using-make ()
		 "Construct arguments to pass to F* by calling make."
		 (with-demoted-errors "Error when constructing arg string: %S"
		   (split-string
		    (car (last (process-lines "make"
					      "-C" (append (getenv "FSTAR_SOURCES_ROOT") "/src")
					      "-f" "Makefile.edit" "--quiet"
					      (concat (file-name-nondirectory buffer-file-name) "-dev")
					      )
			       )
			 )
		    )
		   )
		 )
	       (setq fstar-subp-prover-args #'my-fstar-compute-prover-args-using-make)
	       )
	)
  )
 )
'';
      makefile_edit = ''
FSTAR_HOME = ..
include Makefile.boot.common
ABS_CACHE_DIR = $(abspath $(CACHE_DIR))
%.fsi-dev: $(ABS_CACHE_DIR)/%.fsi.checked.lax
	@echo $(FSTAR_BOOT_OPTIONS)
%.fs-dev: $(ABS_CACHE_DIR)/%.fs.checked.lax
	@echo $(FSTAR_BOOT_OPTIONS)'';
    in
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
                      chmod +x ./bin/fstar.exe'')
                  (pkgs.writeScriptBin "generate-ocaml" ''make ocaml -C src -j6'')
                  (pkgs.writeScriptBin "build-ocaml"
                    ''{rm ./bin/fstar.exe.old || true} &> /dev/null
                      mv ./bin/fstar.exe ./bin/fstar.exe.old
                      if make -C src/ocaml-output ../../bin/fstar.exe; then
                        rm ./bin/fstar.exe.old;
                      else
                        mv ./bin/fstar.exe.old ./bin/fstar.exe
                      fi
                  '')
                ];
                shellHook = ''
                  bash fstar-missing-files/copy.sh || true
                  rm ./bin/fstar.exe || true
                  cp  --no-preserve=all ${fstar}/bin/fstar.exe ./bin/fstar.exe
                  chmod +x ./bin/fstar.exe
                  export FSTAR_SOURCES_ROOT="$(pwd)"
                  echo ${lib.escapeShellArg makefile_edit} > src/Makefile.edit
                  echo ${lib.escapeShellArg dir_locals} > .dir-locals.el
                '';
              };
            }
        );
}
