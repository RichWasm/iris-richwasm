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

          # for compcert
          targets = {
            x86_64-linux = "x86_64-linux";
            aarch64-linux = "aarch64-linux";
            x86_64-darwin = "x86_64-macos";
            aarch64-darwin = "aarch64-macos";
            riscv32-linux = "rv32-linux";
            riscv64-linux = "rv64-linux";
          };

          target =
            targets.${pkgs.stdenv.hostPlatform.system}
              or (throw "Unsupported system: ${pkgs.stdenv.hostPlatform.system}");

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

          # TODO(owen): remove when 3.16 is supported by nixpkgs
          # below is adapted from nixpkgs
          compcert = coqPackages.mkCoqDerivation {

            pname = "compcert";
            owner = "AbsInt";

            version = "3.16";
            releaseRev = v: "v${v}";

            release."3.16".sha256 = "sha256-Ep8bcSFs3Cu+lV5qgo89JJU2vh4TTq66Or0c4evo3gM=";

            strictDeps = true;

            nativeBuildInputs =
              with pkgs;
              with ocamlPackages;
              [
                makeWrapper
                ocaml
                findlib
                menhir
                coq
                coq2html
              ];
            buildInputs = with ocamlPackages; [ menhirLib ];
            propagatedBuildInputs = with coqPackages; [
              flocq
              MenhirLib
            ];

            enableParallelBuilding = true;

            postPatch = ''
              substituteInPlace ./configure \
                --replace \$\{toolprefix\}ar 'ar' \
                --replace '{toolprefix}gcc' '{toolprefix}cc'
            '';

            configurePhase = ''
              ./configure -clightgen \
              -prefix $out \
              -coqdevdir $lib/lib/coq/${coq.coq-version}/user-contrib/compcert/ \
              -toolprefix ${pkgs.stdenv.cc}/bin/ \
              -use-external-Flocq \
              -use-external-MenhirLib \
              ${target} \
            ''; # don't remove the \ above, the command gets appended in override below

            installTargets = "documentation install";
            installFlags = [ ]; # trust ./configure
            preInstall = ''
              mkdir -p $out/share/man
              mkdir -p $man/share
            '';
            postInstall = ''
              # move man into place
              mv $out/share/man/ $man/share/

              # move docs into place
              mkdir -p $doc/share/doc/compcert
              mv doc/html $doc/share/doc/compcert/

              # wrap ccomp to undefine _FORTIFY_SOURCE; ccomp invokes cc1 which sets
              # _FORTIFY_SOURCE=2 by default, but undefines __GNUC__ (as it should),
              # which causes a warning in libc. this suppresses it.
              for x in ccomp clightgen; do
                wrapProgram $out/bin/$x --add-flags "-U_FORTIFY_SOURCE"
              done
            '';

            outputs = [
              "out"
              "lib"
              "doc"
              "man"
            ];
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
                compcert
              ]
              ++ (with coqPackages; [
                parseque
                iris
                coq-elpi
                ExtLib
                ITree
                hierarchy-builder
                mathcomp
                mathcomp-ssreflect
                coq-record-update
              ])
              ++ (with ocamlPackages; [
                zarith
                base
                ppx_import
                ppx_deriving
                janeStreet.ppx_sexp_conv
                janeStreet.sexplib
                janeStreet.ppx_let
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
