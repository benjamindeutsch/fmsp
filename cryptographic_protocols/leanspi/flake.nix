{
  description = "leanspi";
  inputs = { utils.url = "github:numtide/flake-utils"; };
  outputs = { self, nixpkgs, utils }:
    utils.lib.eachDefaultSystem (system:
      let pkgs = nixpkgs.legacyPackages.${system};
      in {
        devShell = pkgs.mkShell {
          name = "leanspi";
          buildInputs = with pkgs; [ elan nixd ] ++ lib.optional (stdenv.isDarwin) git;
        };
        formatter = pkgs.nixfmt;
      });
}
