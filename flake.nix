{
  description = "Category theory for denotational design";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs?ref=23.05";
    utils.url = "github:numtide/flake-utils";
    agda-stdlib-src = {
      url = "github:agda/agda-stdlib?ref=7c5f3ff";
      flake = false;
    };
  };

  outputs = { self, nixpkgs, utils, agda-stdlib-src }:
    utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        standard-library = pkgs.agdaPackages.standard-library.overrideAttrs (final: prev: {
          version = "2.0";
          src = agda-stdlib-src;
        });
        agdaWithStandardLibrary = pkgs.agda.withPackages (_: [ standard-library ]);

      in {
        devShell = pkgs.mkShell {
          buildInputs = [
            agdaWithStandardLibrary
            pkgs.graphviz
          ];
        };

        packages.default = pkgs.agdaPackages.mkDerivation {
          pname = "felix";
          version = "0.0.1";
          src = ./.;

          buildInputs = [ standard-library ];

          everythingFile = "./src/Felix/All.agda";

          meta = with pkgs.lib; {
            description = "Category theory for denotational design";
            homepage = "https://github.com/conal/felix";
            # no license file, all rights reserved?
            # license = licenses.mit;
            # platforms = platforms.unix;
            # maintainers = with maintainers; [ ];
          };
        };
      }
    );
}