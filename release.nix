# You can build this repository using Nix by running:
#
#     $ nix-build release.nix
#
# You can also open up this repository inside of a Nix shell by running:
#
#     $ nix-shell
#
# ... and then Nix will supply the correct Haskell development environment for
# you
{ compiler ? "ghc864" }:
let 
  config = {
    packageOverrides = pkgs: rec {
      haskellPackages = pkgs.haskell.packages // {
        "${compiler}" = pkgs.haskell.packages."${compiler}".override {
          overrides = haskellPackagesNew: haskellPackagesOld: rec {
            hs-reasoner =
              let
                devDeps = with haskellPackagesOld; if pkgs.lib.inNixShell then [ hlint ghcid doctest pkgs.gitg ] else [ ];
                devSystemDeps = if pkgs.lib.inNixShell then [ pkgs.entr ] else [ ];
              in
                haskellPackagesNew.callPackage ./default.nix { inherit devDeps; inherit devSystemDeps; };
          };
        };
      };
    };
  };
  pkgs = import (import ./nix/pinned-nixpkgs.nix) { inherit config; };
in
{
  hs-reasoner = pkgs.haskellPackages.${compiler}.hs-reasoner;
}
