{
  description = "Category theory for denotational design";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-25.05";
    utils.url = "github:numtide/flake-utils";
  };

  outputs =
    {
      self,
      nixpkgs,
      utils,
    }:
    utils.lib.eachDefaultSystem (
      system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        agdaWithStandardLibrary = pkgs.agda.withPackages (p: [ p.standard-library ]);

      in
      {

        formatter = pkgs.nixfmt-rfc-style;

        checks.whitespace = pkgs.stdenvNoCC.mkDerivation {
          name = "check-whitespace";
          dontBuild = true;
          src = ./.;
          doCheck = true;
          checkPhase = ''
            ${pkgs.haskellPackages.fix-whitespace}/bin/fix-whitespace --check
          '';
          installPhase = ''mkdir "$out"'';
        };

        devShells.default = pkgs.mkShell {
          buildInputs = [
            agdaWithStandardLibrary
            pkgs.graphviz
            pkgs.haskellPackages.fix-whitespace
          ];
        };

        packages.default = pkgs.agdaPackages.mkDerivation {
          pname = "felix";
          version = "0.0.1";
          src = ./.;

          buildInputs = with pkgs.agdaPackages; [ standard-library ];

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
