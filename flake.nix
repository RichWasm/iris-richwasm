{
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-26.05";
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
        # NOTE: dune 3.23+ since `rocq.theory` needs `rocq c --config`, previous versions were bugged
        dune_3_23_1 = pkgs.dune_3.overrideAttrs (
          finalAttrs: _: {
            version = "3.23.1";
            src = pkgs.fetchurl {
              url = "https://github.com/ocaml/dune/releases/download/${finalAttrs.version}/dune-${finalAttrs.version}.tbz";
              hash = "sha256-k7TnFX9rqP62HPxfhgCO/SxZA3unigF9krSr8wYyNI8=";
            };
          }
        );

        # NOTE: Some dependencies (rocq-autosubst-ocaml, coq-compcert) require OCaml 4.
        ocamlPackages = pkgs.ocaml-ng.ocamlPackages_4_14;

        ocaml = ocamlPackages.ocaml;
        rocqPackages = pkgs.rocqPackages_9_0.overrideScope (
          final: prev: {
            rocq-core = prev.rocq-core.override { customOCamlPackages = ocamlPackages; };
            dune = dune_3_23_1;
            vsrocq-language-server = prev.vsrocq-language-server.override { coq = coqPackages.coq; };
          }
        );
        rocq = rocqPackages.rocq-core;
        coqPackages = pkgs.coqPackages_9_0.overrideScope (
          final: prev: {
            coq = prev.coq.override {
              customOCamlPackages = ocamlPackages;
              inherit rocqPackages;
            };
            dune = dune_3_23_1;
          }
        );
      };
    in
    {
      packages = eachSystem (
        system:
        let
          pkgs = pkgsFor.${system};
          inherit (pinned-versions pkgs) coqPackages rocqPackages ocamlPackages;

          iris-richwasm-deps =
            [ ]
            ++ (with rocqPackages; [
              stdlib
              iris
              mathcomp
              mathcomp-boot
              mathcomp-order

              rocq-elpi

              hierarchy-builder

              parseque
            ])
            ++ (with coqPackages; [
              compcert
              ITree
              ExtLib

              coq-record-update
              flocq
              autosubst-ocaml
            ]);

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

          iris-richwasm-build =
            (rocqPackages.mkRocqDerivation {
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

              preBuild = ''
                export DUNE_CACHE=disabled
              '';

              buildInputs = [
              ]
              ++ iris-richwasm-deps
              ++ richwasm-ocaml-deps;

              passthru.devShellDeps = [
              ]
              ++ iris-richwasm-deps
              ++ richwasm-ocaml-deps
              ++ richwasm-test-deps;

              passthru.testDeps = richwasm-test-deps;
            }).overrideAttrs
              (old: {
                pname = project + "-build";

                dontStrip = true;
                dontPatchELF = true;

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

          outputs = [ "out" ];
          postBuild = "";

          buildInputs = old.buildInputs ++ old.passthru.testDeps;

          doCheck = true;

          patchPhase = ''
            mkdir -p _build
            # NOTE: keep mode so we don't strip executable bit
            cp -rT --no-preserve=ownership ${pkgs.iris-richwasm-build.build}/_build _build
            chmod -R u+w _build
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
            rocq
            rocqPackages
            coqPackages
            ocaml
            ocamlPackages
            dune_3_23_1
            ;
          inherit (pkgs.stdenv.hostPlatform) system;

        in
        {
          default = pkgs.mkShell {
            packages = [
              rocq
              ocaml
              dune_3_23_1
            ]
            ++ (with pkgs; [
              nixd
              nil
              nixfmt
            ])
            ++ (with rocqPackages; [
              vsrocq-language-server
            ])
            ++ (with coqPackages; [
              coq-lsp
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
