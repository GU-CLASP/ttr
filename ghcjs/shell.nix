{ nixpkgs ? import <nixpkgs> {}, compiler ? "ghcjsHEAD" }:
let nixpkgs_source =
  nixpkgs.fetchFromGitHub {
      owner = "NixOS";
      repo = "nixpkgs";
      rev = "f7b97df2cd9fa82968c1c43ee357457a5b0adbf5";
      sha256 = "06l4vy7hbcyv3w016ry7pv4qkd0mq5qlhixcva9izcwq12a9c5r0";
    };
  nixpkgs' = (import nixpkgs_source){};
in with nixpkgs'.pkgs;
let
 hp = haskell.packages.${compiler}.override{
    overrides = self: super: {
      pretty-compact = self.callPackage ./pretty-compact.nix {};
#      ghcjs-dom-jsffi = self.callPackage ./ghcjs-dom-jsffi.nix {};
#      ghcjs-dom = self.callPackage ./ghcjs-dom.nix {};
#      ghcjs-dom-jsaddle = self.callPackage ./ghcjs-dom-jsaddle.nix {};
#      jsaddle-dom = self.callPackage ./jsaddle-dom.nix {};
    };};
 ghc = hp.ghcWithPackages (ps: with ps; [array base containers gasp mtl pretty-compact transformers ghcjs-dom-jsffi]);
in
pkgs.stdenv.mkDerivation {
  name = "my-haskell-env-0";
  buildInputs = [ ghc ];
  shellHook = "eval $(egrep ^export ${ghc}/bin/ghc)";
}
