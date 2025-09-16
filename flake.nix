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
          coq = pkgs.coq_9_0;
          coqPackages = pkgs.coqPackages_9_0;
          ocamlPackages = coq.ocamlPackages;
        in
        rec {
          default = self.packages.${pkgs.system}.${project};

          autosubst-ocaml = ocamlPackages.buildDunePackage {
            pname = "rocq-autosubst-ocaml";
            version = "1.1+9.0";

            src = pkgs.fetchFromGitHub {
              owner = "uds-psl";
              repo = "autosubst-ocaml";
              rev = "d289f1d0ee409a6839b39936a682008a883c53c0";
              hash = "sha256-Jru1iu3wZ8OTtdJ1WmVVgkF4/L3PMwgF7c7GkSZCQ/g=";
            };

            buildInputs =
              [
                coq
              ]
              ++ (with ocamlPackages; [
                findlib
                ocamlgraph
                angstrom
                ppx_deriving
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

            buildInputs =
              [
                autosubst-ocaml
              ]
              ++ (with coqPackages; [
                compcert
                parseque
                iris
                coq-elpi
                ExtLib
                ITree
                hierarchy-builder
                mathcomp
                mathcomp-ssreflect
                coq-record-update
                flocq
              ])
              ++ (with ocamlPackages; [
                base
                zarith
                menhir
                ppx_import
                ppx_deriving
                janeStreet.ppx_sexp_conv
                janeStreet.sexplib
                janeStreet.ppx_let
                janeStreet.ppx_expect
              ]);
          };
        }
      );

      devShells = eachSystem (pkgs: {
        default = pkgs.mkShell {
          packages =
            [
              pkgs.git # TODO(ari): figure out how to use system git
            ]
            ++ (with pkgs.coqPackages; [
              vscoq-language-server
            ])
            ++ (with pkgs.coq.ocamlPackages; [
              merlin
              ocp-indent
              ocamlformat
              ocaml-lsp
              utop
            ]);

          inputsFrom = [
            self.packages.${pkgs.system}.${project}
          ];
        };
      });
    };
}
