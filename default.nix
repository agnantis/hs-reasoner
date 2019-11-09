{ mkDerivation, stdenv, base, containers, criterion, hspec, microlens-platform, mtl
, polysemy, polysemy-plugin, recursion-schemes, template-haskell, QuickCheck
, devDeps ? [ ]
, devSystemDeps ? [ ]
}:
mkDerivation {
  pname = "hs-reasoner";
  version = "0.1.0.0";
  src= ./.;
  isLibrary = true;
  isExecutable = true;
  buildDepends = devSystemDeps;
  libraryHaskellDepends = [
    base containers criterion hspec microlens-platform mtl polysemy
    polysemy-plugin recursion-schemes template-haskell QuickCheck
  ] ++ devDeps;
  executableHaskellDepends = [ base ];
  homepage = "https://github.com/agnantis/hs-reasoner";
  license = stdenv.lib.licenses.bsd3;
}
