{
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  };

  outputs =
    {
      self,
      nixpkgs,
      systems,
    }:
    let
      project = "iris-richwasm";
      version = "0.1.0";
      lib = nixpkgs.lib;
      eachSystem =
        f:
        lib.genAttrs (import systems) (
          system:
          f (
            import nixpkgs {
              inherit system;
              config.allowUnfree = true; # compcert
            }
          )
        );
    in
    {
      packages = eachSystem (
        pkgs:
        let
          ocamlPackages = pkgs.ocaml-ng.ocamlPackages_4_14;
          coq = pkgs.coq_8_20;
          coqPackages = pkgs.coqPackages_8_20;
        in
        {
          default = self.packages.${pkgs.system}.${project};

          parseque = coqPackages.mkCoqDerivation {
            pname = "parseque";

            version = "0.2.2";
            release = {
              broken = false;
            };
            enableParallelBuilding = true;

            src = pkgs.fetchFromGitHub {
              owner = "rocq-community";
              repo = "parseque";
              rev = "v0.2.2";
              hash = "sha256-O50Rs7Yf1H4wgwb7ltRxW+7IF0b04zpfs+mR83rxT+E=";
            };
          };

          vscoq-language-server = ocamlPackages.buildDunePackage rec {
            pname = "vscoq-language-server";
            version = "2.2.6";

            src =
              let
                fetched = pkgs.fetchFromGitHub {
                  owner = "coq-community";
                  repo = "vscoq";
                  rev = "v${version}";
                  hash = "sha256-J8nRTAwN6GBEYgqlXa2kkkrHPatXsSObQg9QUQoZhgE=";
                };
              in
              "${fetched}/language-server";
            nativeBuildInputs = [ coq ];
            buildInputs =
              [
                coq
                pkgs.glib
                pkgs.adwaita-icon-theme
                pkgs.wrapGAppsHook3
              ]
              ++ (with ocamlPackages; [
                findlib
                lablgtk3-sourceview3
                yojson
                zarith
                ppx_inline_test
                ppx_assert
                ppx_sexp_conv
                ppx_deriving
                ppx_import
                sexplib
                ppx_yojson_conv
                lsp
                sel
                ppx_optcomp
              ]);
          };

          ${project} = coqPackages.mkCoqDerivation {
            pname = project;
            version = version;

            namePrefix = [ ];

            src = ./.;
            useDune = true;

            preBuild = ''
              export DUNE_CACHE=disabled
            '';

            nativeBuildInputs = [
              coq
            ];

            buildInputs = [
              coqPackages.iris
              coqPackages.coq-elpi
              coqPackages.ExtLib
              coqPackages.ITree
              pkgs.compcert
              self.packages.${pkgs.system}.parseque
              coqPackages.hierarchy-builder
              coqPackages.mathcomp
              coqPackages.mathcomp-ssreflect
              ocamlPackages.zarith
            ];
          };
        }
      );

      devShells = eachSystem (pkgs: {
        default = pkgs.mkShell {
          packages = [
            pkgs.git # TODO: figure out how to use system git
            self.packages.${pkgs.system}.vscoq-language-server
          ];

          inputsFrom = [
            self.packages.${pkgs.system}.${project}
          ];
        };
      });
    };
}
