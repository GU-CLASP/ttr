# ttr
A type theory with records

This project is built with the Styx tool. Install styx:

nix-env -iA nixpkgs.haskellPackages.styx
nix-env -iA nixpkgs.cabal2nix

Then

styx configure
styx build
styx exec -- ttr <arguments>

