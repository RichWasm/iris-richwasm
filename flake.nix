{
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
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
              overlays = [ ];
            }
          )
        );

      pinned-versions = pkgs: rec {
        coq = pkgs.coq_9_0;
        coqPackages = pkgs.coqPackages_9_0;
        ocamlPackages = coq.ocamlPackages;
        ocaml = ocamlPackages.ocaml;
      };
    in
    {
      packages = eachSystem (
        pkgs:
        let
          inherit (pinned-versions pkgs) coqPackages ocamlPackages;

          iris-wasm-deps = with coqPackages; [
            stdlib
            iris
            compcert
            mathcomp
            ITree
            parseque
          ];

          iris-richwasm-deps = with coqPackages; [
            coq-elpi
            ExtLib
            hierarchy-builder
            mathcomp-ssreflect
            coq-record-update
            flocq
            autosubst-ocaml
          ];

          richwasm-ocaml-deps = with ocamlPackages; [
            base
            core
            core_unix
            zarith
            ppx_import
            ppx_deriving
            janeStreet.ppx_sexp_conv
            janeStreet.ppx_let
            janeStreet.ppx_expect
            janeStreet.ppx_variants_conv
            janeStreet.sexplib
            janeStreet.parsexp
          ];
        in
        rec {
          default = self.packages.${pkgs.system}.${project};

          # NOTE(owen): this doesn't need to be seperate but since it rarely
          # chanages, it greatly reduces build time
          iris-wasm = coqPackages.mkCoqDerivation {
            pname = "iris-wasm";
            version = "2.0";

            namePrefix = [ ];

            src = ./vendor/iriswasm;
            useDune = true;

            propagatedBuildInputs = iris-wasm-deps;
            meta.excludeFromDevShell = true;
          };

          ${project} = coqPackages.mkCoqDerivation {
            pname = project;
            version = version;

            namePrefix = [ ];

            src = ./.;
            useDune = true;

            postPatch = ''
              sed -i '/(vendored_dirs vendor)/d' dune
            '';

            preBuild = ''
              export DUNE_CACHE=disabled
            '';

            buildInputs =
              [
                iris-wasm
              ]
              ++ iris-richwasm-deps
              ++ richwasm-ocaml-deps;

            # NOTE(owen): let dune manage the iris-wasm vendor in the devshell
            passthru.devShellDeps =
              [
              ]
              ++ iris-wasm-deps
              ++ iris-richwasm-deps
              ++ richwasm-ocaml-deps;
          };
        }
      );

      devShells = eachSystem (
        pkgs:
        let
          inherit (pinned-versions pkgs)
            coq
            coqPackages
            ocaml
            ocamlPackages
            ;
          inherit (pkgs) system;
        in
        {
          default = pkgs.mkShell {
            packages =
              [
                pkgs.git
                pkgs.dune_3
                pkgs.wabt
                coq
                ocaml
              ]
              ++ (with coqPackages; [
                vscoq-language-server
              ])
              ++ (with ocamlPackages; [
                merlin
                ocp-indent
                ocamlformat
                ocaml-lsp
                utop
              ])
              ++ self.packages.${system}.${project}.passthru.devShellDeps;
          };
        }
      );
    };
}
