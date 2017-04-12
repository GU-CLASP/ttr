{ mkDerivation, base, containers, fetchgit, stdenv }:
mkDerivation {
  pname = "pretty-compact";
  version = "2.0";
  src = fetchgit {
    url = "https://github.com/jyp/prettiest.git";
    sha256 = "09dcni3a8wprc9hj3l2cyhizzjqdanm2bl6pmhgba4vlpbdyqiqb";
    rev = "b28aabccf1274713a20f43bed84eec25e6eea89d";
  };
  libraryHaskellDepends = [ base containers ];
  description = "Pretty-printing library";
  license = "GPL";
}
