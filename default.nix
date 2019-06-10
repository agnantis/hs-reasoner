{ mkDerivation, base, extensible-effects, log-effect, stdenv, devDeps ? [ ], devSystemDeps ? [ ]
}:
mkDerivation {
  pname = "hs-reasoner";
  version = "0.1.0.0";
  src = ./.;
  isLibrary = true;
  isExecutable = true;
  buildDepends = devSystemDeps;
  libraryHaskellDepends = [ base extensible-effects log-effect ] ++ devDeps;
  executableHaskellDepends = [ base ];
  homepage = "https://github.com/agnantis/hs-reasoner";
  license = stdenv.lib.licenses.bsd3;
}
