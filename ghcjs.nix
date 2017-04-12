{ nixpkgs ? import <nixpkgs> {}, compiler ? "ghcjsHEAD" }:
let nixpkgs_source =
  nixpkgs.fetchFromGitHub {
      owner = "NixOS";
      repo = "nixpkgs";
      rev = "a05959e191c8bef969fd84a8dce0343ef6dcd7e0";
      sha256 = "1bhafnl0g5jmqgagvq9zvw3qh8v2hc13glyn90r8mmjywblkyy71";
    };
  nixpkgs' = (import nixpkgs_source){};
in with nixpkgs'.pkgs;
let
 hp = haskell.packages.${compiler}.override{
    overrides = self: super: {
      pretty-compact = self.callPackage ./pretty-compact.nix {};
      };};
 ghc = hp.ghcWithPackages (ps: with ps; [array base containers gasp mtl pretty-compact transformers ghcjs-dom]);
in
pkgs.stdenv.mkDerivation {
  name = "my-haskell-env-0";
  buildInputs = [ ghc ];
  shellHook = "eval $(egrep ^export ${ghc}/bin/ghc)";
}
