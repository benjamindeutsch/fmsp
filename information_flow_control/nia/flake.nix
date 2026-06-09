{
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/25.11";
    flake-utils.url = "github:numtide/flake-utils";
  };
  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let pkgs = nixpkgs.legacyPackages.${system}; in
      let parsec = pkgs.python3Packages.buildPythonPackage rec {
            pname = "parsec";
            version = "3.17";
            src = pkgs.fetchurl {
              url = "https://files.pythonhosted.org/packages/50/70/fd65d87ab0afe9a669bb5b018fd5176749496086e38d2a4103efbe6c8bd8/parsec-3.17.tar.gz";
              sha256 = "0lza5b4v5sw5y4ny860ay0mxyrahlkygk23vi3jw511iyi5dcj4p";
            };
            format = "setuptools";
            doCheck = false;
            buildInputs = [];
            checkInputs = [];
            nativeBuildInputs = [
              pkgs.python3Packages."setuptools"
              pkgs.python3Packages."wheel"
            ];
            propagatedBuildInputs = [
              pkgs.python3Packages."setuptools"
            ];
          };
      in {
        devShell = pkgs.mkShell {
          nativeBuildInputs = with pkgs; [ (python3.withPackages(ps: with ps; [ parsec ps.z3-solver ])) z3 ];
          buildInputs = with pkgs; [ ];
        };
      });
}
