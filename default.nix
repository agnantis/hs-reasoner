{ mkDerivation, base, containers, recursion-schemes, extensible-effects, microlens-platform, mtl
, template-haskell, stdenv, devDeps ? [ ], devSystemDeps ? [ ]
}:
mkDerivation {
  pname = "hs-reasoner";
  version = "0.1.0.0";
  src = ./.;
  isLibrary = true;
  isExecutable = true;
  buildDepends = devSystemDeps;
  libraryHaskellDepends = [ base containers extensible-effects microlens-platform mtl recursion-schemes template-haskell ] ++ devDeps;
  executableHaskellDepends = [ base ];
  homepage = "https://github.com/agnantis/hs-reasoner";
  license = stdenv.lib.licenses.bsd3;
}
