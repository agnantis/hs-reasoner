{ mkDerivation, base, containers, hspec, recursion-schemes, extensible-effects, microlens-platform, mtl
, QuickCheck, template-haskell, polysemy, polysemy-plugin, stdenv, devDeps ? [ ], devSystemDeps ? [ ]
}:
mkDerivation {
  pname = "hs-reasoner";
  version = "0.1.0.0";
  src = ./.;
  isLibrary = true;
  isExecutable = true;
  buildDepends = devSystemDeps;
  libraryHaskellDepends = [ base containers extensible-effects polysemy polysemy-plugin hspec microlens-platform mtl recursion-schemes QuickCheck template-haskell ] ++ devDeps;
  executableHaskellDepends = [ base ];
  homepage = "https://github.com/agnantis/hs-reasoner";
  license = stdenv.lib.licenses.bsd3;
}
