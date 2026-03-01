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
      inherit (nixpkgs.lib) genAttrs fileset;
      eachSystem = genAttrs (import systems);
      pkgsFor = eachSystem (
        system:
        import nixpkgs {
          inherit system;
          config.allowUnfree = true; # compcert
          overlays = [ ];
        }
      );
      eachPkgs = f: eachSystem (s: f (pkgsFor.${s} // self.packages.${s}));
      pinned-versions = pkgs: rec {
        coq = pkgs.coq_9_0;
        coqPackages = pkgs.coqPackages_9_0;
        ocamlPackages = coq.ocamlPackages;
        ocaml = ocamlPackages.ocaml;
      };
    in
    {
      packages = eachSystem (
        system:
        let
          pkgs = pkgsFor.${system};
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
            mathcomp-boot
            mathcomp-order
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
            janeStreet.ppx_variants_conv
            janeStreet.sexplib
            janeStreet.parsexp
            pkgs.wabt
            alcotest
            ocolor
          ];

          richwasm-test-deps = with pkgs; [
            nodejs_24
            ocamlPackages.janeStreet.ppx_expect
          ];
        in
        rec {
          default = iris-richwasm;

          # NOTE(owen): this doesn't need to be separate but since it rarely
          # changes, it greatly reduces build time
          iris-wasm = coqPackages.mkCoqDerivation {
            pname = "iris-wasm";
            version = "2.0";

            namePrefix = [ ];

            src = ./vendor/iriswasm;
            useDune = true;

            propagatedBuildInputs = iris-wasm-deps;
            meta.excludeFromDevShell = true;
          };

          iris-richwasm-build =
            (coqPackages.mkCoqDerivation {
              pname = project;
              version = version;

              namePrefix = [ ];

              src = fileset.toSource {
                root = ./.;
                fileset = fileset.unions [
                  ./bin
                  ./src
                  ./tests
                  ./theories
                  ./dune
                  ./dune-project
                  ./iris-richwasm.opam
                ];
              };
              useDune = true;

              postPatch = ''
                sed -i '/(vendored_dirs vendor)/d' dune
              '';

              preBuild = ''
                export DUNE_CACHE=disabled
              '';

              buildInputs = [
                iris-wasm
              ]
              ++ iris-wasm-deps
              ++ iris-richwasm-deps
              ++ richwasm-ocaml-deps;

              # NOTE(owen): let dune manage the iris-wasm vendor in the devshell
              passthru.devShellDeps = [
              ]
              ++ iris-wasm-deps
              ++ iris-richwasm-deps
              ++ richwasm-ocaml-deps
              ++ richwasm-test-deps;

              passthru.testDeps = richwasm-test-deps;
            }).overrideAttrs
              (old: {
                pname = project + "-build";

                outputs = [
                  "out"
                  "build"
                ];
                postBuild = (old.postBuild or "") + ''
                  mkdir -p $build
                  cp -r _build $build/_build
                '';
              });

          iris-richwasm = pkgs.stdenv.mkDerivation {
            pname = project;
            version = version;
            src = iris-richwasm-build;
            dontBuild = true;

            installPhase = ''
              rm -rf build
              cp -r . $out
            '';

            passthru.devShellDeps = iris-richwasm-build.passthru.devShellDeps;
          };
        }
      );

      checks = eachPkgs (pkgs: {
        default = pkgs.iris-richwasm-build.overrideAttrs (old: {
          pname = project + "-check";
          name = project + "-check";

          buildInputs = old.buildInputs ++ old.passthru.testDeps;

          doCheck = true;

          patchPhase = ''
            mkdir -p _build
            cp -rT --no-preserve=mode,ownership ${pkgs.iris-richwasm-build.build}/_build _build
          '';

          buildPhase = "";

          checkPhase = ''
            runHook preCheck
            dune runtest --no-buffer
            runHook postCheck
          '';

          installPhase = ''
            mkdir -p $out
          '';
        });
      });

      devShells = eachPkgs (
        pkgs:
        let
          inherit (pinned-versions pkgs)
            coq
            coqPackages
            ocaml
            ocamlPackages
            ;
          inherit (pkgs.stdenv.hostPlatform) system;
        in
        {
          default = pkgs.mkShell {
            packages = [
              coq
              ocaml
            ]
            ++ (with pkgs; [
              dune_3
              nixd
              nil
              nixfmt
            ])
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

            shellHook = ''
              unset DEVELOPER_DIR
              # npm install --package-lock-only
              # npm ci
            '';
          };
        }
      );
    };
}
