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
                ghcide = (import (builtins.fetchTarball "https://github.com/hercules-ci/ghcide-nix/tarball/master") {}).ghcide-ghc864;
                # uncomment to use haskell-ide-engine (not working for cabal 3)
                #all-hies = import (fetchTarball "https://github.com/infinisil/all-hies/tarball/master") {};
                #hie-864 = (all-hies.selection { selector = p: { inherit (p) ghc864; }; });
                devDeps = with haskellPackagesOld; if pkgs.lib.inNixShell then [ hlint ghcid doctest pkgs.gitg Cabal_2_4_1_0 ] else [ ];
                devSystemDeps = if pkgs.lib.inNixShell then [ pkgs.entr ghcide hie-864 ] else [ ];
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
