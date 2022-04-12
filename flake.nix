{
  description = "Project Everest";

  inputs = {
    nixpkgs.url = "nixpkgs";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
  let
    systems = [ "x86_64-linux" ];
  in flake-utils.lib.eachSystem systems (system:
    let
      pkgs = import nixpkgs { inherit system; };
      z3 = pkgs.callPackage ./z3.nix {};
      mlcrypto = pkgs.callPackage ./mlcrypto.nix {};
      fstar = pkgs.callPackage ./default.nix {
        inherit z3 mlcrypto;
        ocamlPackages = pkgs.ocaml-ng.ocamlPackages_4_12;
      };
    in {
      packages = {
        inherit z3 mlcrypto fstar;
      };
      defaultPackage = fstar;
      hydraJobs = {
        fstar-build = fstar;
      };
    }
  );
}
