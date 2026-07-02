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

        # NOTE: despite the recommendations online claiming that one should use ocaml 4 for rocq,
        # there doesn't seem to be any real-world performance difference. I tried comparing
        # ocamlPackages_5_3 and ocamlPackages_4_14 and produced the following results using `time`:
        # - ocaml 5: nix flake check -LL 2.93s user 0.59s system 0% cpu 12:39.59 total
        # - ocaml 4: nix flake check -LL 3.00s user 0.64s system 0% cpu 12:34.31 total
        # Using ocaml 5 uniformly makes everything much simpler so that is what is specified below:
        ocamlPackages = pkgs.ocaml-ng.ocamlPackages_5_4.overrideScope (
          # vsrocq's ppx_yojson_conv pins yojson_2 (2.2.2) while its lsp uses yojson 3.0.0 — collide in findlib.
          _: prev: { yojson_2 = prev.yojson; }
        );

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
              # NOTE: compcert works fine with ocaml 5, they just don't officially support it;
              # but we are using it at the rocq level anyways, so it doesn't really matter.
              (compcert.overrideAttrs (o: {
                configurePhase = ''
                  ${o.configurePhase} \
                    -ignore-ocaml-version
                '';
              }))
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
