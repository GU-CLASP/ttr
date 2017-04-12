{ nixpkgs ? import <nixpkgs> {}, compiler ? "ghc7102" }:
let
  inherit (nixpkgs) pkgs;
  hp = pkgs.haskellPackages
    # .override {
    #   overrides = self: super: {
    #     mkDerivation = args: super.mkDerivation (args // {
    #       enableSharedExecutables = false;
    #       enableSharedLibraries = false;
    #     });
    #   };
    # }
    ;
  ghc = hp.ghcWithPackages (ps: with ps; [stack alex happy hscolour]);
in
pkgs.stdenv.mkDerivation {
  name = "my-haskell-env-0";
  buildInputs = [ ghc pkgs.gmp4 ];
  shellHook = "eval $(egrep ^export ${ghc}/bin/ghc)";
}
