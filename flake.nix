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

          richwasm-web-deps = [
            pkgs.esbuild
          ]
          ++ (with ocamlPackages; [
            js_of_ocaml-compiler
            js_of_ocaml
            brr
            zarith_stubs_js
          ]);
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
              ++ richwasm-test-deps
              ++ richwasm-web-deps;

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

          docker =
            let
              shell = pkgs.dockerTools.streamNixShellImage {
                name = project;
                tag = "latest";
                drv = pkgs.mkShell {
                  name = project;
                  inputsFrom = [ self.devShells.${system}.default ];
                  packages = with pkgs; [
                    less
                    neovim
                    emacs-nox
                    nano
                    git
                    which
                    procps
                    python3
                  ];
                  shellHook = ''
                    if [ ! -d ~/iris-richwasm ]; then
                      cp -r ${self} ~/iris-richwasm
                      chmod -R u+w ~/iris-richwasm
                    fi
                    cd ~/iris-richwasm
                  '';
                };
              };
              # HACK: streamNixShellImage has no /tmp, https://github.com/NixOS/nixpkgs/issues/257172
              rootLayer = pkgs.runCommand "${project}-root-layer" { nativeBuildInputs = [ pkgs.jq ]; } ''
                mkdir -p $out root/tmp
                chmod 1777 root/tmp
                install -m 644 "$(jq -r .customisation_layer ${shell.conf})/layer.tar" $out/layer.tar
                tar -rf $out/layer.tar -C root --owner=0 --group=0 --mtime="@$SOURCE_DATE_EPOCH" ./tmp
                sha256sum $out/layer.tar | cut -d ' ' -f 1 > $out/checksum
              '';
              conf = pkgs.runCommand "${project}-conf.json" { nativeBuildInputs = [ pkgs.jq ]; } ''
                jq --arg layer ${rootLayer} '.customisation_layer = $layer' ${shell.conf} > $out
              '';
            in
            pkgs.runCommand "${project}.tar.gz" { nativeBuildInputs = [ pkgs.pigz ]; } ''
              ${shell.streamScript} ${conf} | pigz -p$NIX_BUILD_CORES -nTR > $out
            '';

          vm =
            let
              nixos = nixpkgs.lib.nixosSystem {
                specialArgs = { inherit self; };
                modules = [
                  { nixpkgs.pkgs = pkgs; }
                  ./nix/vm.nix
                ];
              };
              inherit (nixos.config.system.build) image;
              sourceLabel = nixos.config.fileSystems."/mnt/iris-richwasm".label;
              sourceSize = "1G";
              # virtualbox is only packaged for x86_64-linux
              x86 = pkgsFor.x86_64-linux;
              vbox =
                {
                  x86_64-linux = {
                    platform = "x86";
                    ostype = "Linux_64";
                    controller = "SATA";
                  };
                  aarch64-linux = {
                    platform = "arm";
                    ostype = "Linux_arm64";
                    controller = "VirtioSCSI";
                  };
                }
                .${system};
              appliance =
                x86.runCommand "${project}-appliance-${system}"
                  {
                    nativeBuildInputs = with x86; [
                      zstd
                      qemu-utils
                      virtualbox
                    ];
                  }
                  ''
                    export HOME=$PWD
                    zstd -d ${image}/${nixos.config.image.fileName} -o disk.raw
                    qemu-img convert -f raw -O vdi disk.raw disk.vdi
                    rm disk.raw
                    VBoxManage modifymedium disk disk.vdi --resize=65536
                    qemu-img create -q -f vdi source.vdi ${sourceSize}
                    VBoxManage createvm --name=${project} --platform-architecture=${vbox.platform} \
                      --ostype=${vbox.ostype} --default --register
                    VBoxManage modifyvm ${project} --firmware=efi --memory=8192 --cpus=4
                    VBoxManage storageattach ${project} --storagectl=${vbox.controller} \
                      --port=0 --device=0 --type=hdd --medium=disk.vdi
                    VBoxManage storageattach ${project} --storagectl=${vbox.controller} \
                      --port=1 --device=0 --type=hdd --medium=source.vdi
                    VBoxManage export ${project} --output=${project}.ova
                    mkdir $out
                    tar -xf ${project}.ova -C $out ${project}.ovf ${project}-disk001.vmdk
                    cd $out && sha1sum --tag ${project}.ovf ${project}-disk001.vmdk > manifest
                  '';
              source =
                x86.runCommand "${project}-source.vmdk"
                  {
                    nativeBuildInputs = with x86; [
                      e2fsprogs
                      qemu-utils
                    ];
                  }
                  ''
                    truncate -s ${sourceSize} source.img
                    mkfs.ext4 -q -L ${sourceLabel} -d ${self} source.img
                    debugfs -w -R 'rmdir lost+found' source.img
                    qemu-img convert -f raw -O vmdk -o subformat=streamOptimized source.img $out
                  '';
            in
            x86.runCommand "${project}-vm" { } ''
              cp ${source} ${project}-disk002.vmdk
              { cat ${appliance}/manifest; sha1sum --tag ${project}-disk002.vmdk; } > ${project}.mf
              mkdir $out
              tar --format=ustar --owner=0 --group=0 --mtime=@$SOURCE_DATE_EPOCH \
                -cf $out/${project}-${system}.ova \
                -C ${appliance} ${project}.ovf ${project}-disk001.vmdk \
                -C $PWD ${project}-disk002.vmdk ${project}.mf
            '';
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
        rec {
          build = pkgs.mkShell {
            packages = [
              rocq
              ocaml
              dune_3_23_1
            ]
            ++ self.packages.${system}.${project}.passthru.devShellDeps;
          };

          default = pkgs.mkShell {
            inputsFrom = [ build ];
            packages = (with pkgs; [
              just
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
            ]);
          };
        }
      );
    };
}
