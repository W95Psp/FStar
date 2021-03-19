let
  pkgs = import <nixpkgs> {};
  fstars = pkgs.fstars;
  factory = fstars.factory;
  fstar = fstars.master-unicode-op;
in
factory.perform-fstar-to-ocaml fstar (factory.fstar-of-sources {
  name = "fstar-my-dev-version";
  src = pkgs.lib.cleanSource ./.;
})

