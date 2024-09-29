{
  description = "F*";

  inputs = {
    flake-utils.url = "github:numtide/flake-utils";
    nixpkgs.url = "github:nixos/nixpkgs/nixos-unstable";
  };

  outputs =
    {
      self,
      flake-utils,
      nixpkgs,
    }:
    flake-utils.lib.eachDefaultSystem (
      system:
      let
        pkgs = import nixpkgs { inherit system; };
        version = self.rev or "dirty";
      in
      {
        packages = rec {
          z3 = pkgs.z3_4_8_5;
          ocamlPackages = pkgs.ocaml-ng.ocamlPackages_4_14;
          /** Dune build of the ocaml snapshot */
          fstar-dune = ocamlPackages.callPackage .nix/dune.nix { inherit version; };
          /** Checked `ulib` */
          fstar-ulib = pkgs.callPackage .nix/ulib.nix { inherit fstar-dune version z3; };
          /** OCaml extraction of F*'s own sources */
          fstar-ocaml-snapshot = pkgs.callPackage .nix/ocaml-snapshot.nix {
            inherit ocamlPackages version z3;
            fstar = fstar-dune;
          };
          /** Bootstraps F* `stage` times */
          staged-fstar-bootstrap = {admit_queries, stage}:
              pkgs.callPackage .nix/bootstrap.nix {
                inherit fstar-dune fstar-ocaml-snapshot fstar-ulib admit_queries stage;
                fstar = pkgs.callPackage .nix/fstar.nix {
            inherit
              fstar-dune
              fstar-ulib
              ocamlPackages
              version
              z3
              ;
          };
              };
          /** Bootstraps F* fully 3 times */
          fstar-bootstrap-stage-3 = staged-fstar-bootstrap {
            stage = 3;
            admit_queries = true;
          };
          /** Bootstraps F* fully 1 time */
          fstar-bootstrap = staged-fstar-bootstrap {
            stage = 1;
            admit_queries = false;
          };
          /** Bootstraps F* 1 time, admitting SMT queries.
              This compiles F* quickly, but does not verify `ulib`.
          */
          fstar-bootstrap-fast = staged-fstar-bootstrap {
            stage = 1;
            admit_queries = true;
          };
          emacs-fstar = pkgs.writeScriptBin "emacs-fstar" ''
            #!${pkgs.stdenv.shell}
            export PATH="${self.packages.${system}.fstar}/bin:$PATH"
            export EMACSLOADPATH=
            ${
              (pkgs.emacsPackagesFor pkgs.emacs).emacsWithPackages (
                epkgs: with epkgs.melpaPackages; [ fstar-mode ]
              )
            }/bin/emacs -q "$@"
          '';
          fstar = fstar-bootstrap-fast;
          default = fstar;
        };

        apps.emacs = {
          type = "app";
          program = "${self.packages.${system}.emacs-fstar}/bin/emacs-fstar";
        };

        devShells.default = pkgs.mkShell {
          name = "${self.packages.${system}.fstar.name}-dev";
          inputsFrom = [ self.packages.${system}.fstar ];
          shellHook = ''
            export FSTAR_SOURCES_ROOT="$(pwd)"
            export PATH="$FSTAR_SOURCES_ROOT/bin/:$PATH"
          '';
        };

        formatter = pkgs.nixfmt-rfc-style;
      }
    );
}
