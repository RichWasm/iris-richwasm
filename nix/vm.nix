{
  self,
  config,
  lib,
  pkgs,
  modulesPath,
  ...
}:
let
  user = "reviewer";
  repo = "/home/${user}/iris-richwasm";
  source = "/mnt/iris-richwasm";
  efiArch = pkgs.stdenv.hostPlatform.efiArch;
  registration = "/nix-path-registration";
  inherit (config.image.repart) partitions;
in
{
  imports = [ "${modulesPath}/image/repart.nix" ];

  image.repart = {
    name = "iris-richwasm";
    compression.enable = true;
    partitions = {
      esp = {
        contents = {
          "/EFI/BOOT/BOOT${lib.toUpper efiArch}.EFI".source =
            "${pkgs.systemd}/lib/systemd/boot/efi/systemd-boot${efiArch}.efi";
          "/EFI/Linux/${config.system.boot.loader.ukiFile}".source =
            "${config.system.build.uki}/${config.system.boot.loader.ukiFile}";
        };
        repartConfig = {
          Type = "esp";
          Format = "vfat";
          Label = "ESP";
          SizeMinBytes = "512M";
        };
      };
      root = {
        storePaths = [ config.system.build.toplevel ];
        contents.${registration}.source = "${
          pkgs.closureInfo { rootPaths = [ config.system.build.toplevel ]; }
        }/registration";
        repartConfig = {
          Type = "root";
          Format = "ext4";
          Label = "nixos";
          Minimize = "guess";
        };
      };
    };
  };
  boot.loader.grub.enable = false;
  boot.growPartition = true;
  fileSystems = {
    "/" = {
      label = partitions.root.repartConfig.Label;
      fsType = "ext4";
      autoResize = true;
    };
    "/boot" = {
      label = partitions.esp.repartConfig.Label;
      fsType = "vfat";
    };
    ${source} = {
      label = "iris-source";
      fsType = "ext4";
      options = [
        "ro"
        "nofail"
      ];
    };
  };

  systemd.services.register-nix-store = {
    unitConfig = {
      DefaultDependencies = false;
      ConditionPathExists = registration;
    };
    wantedBy = [ "sysinit.target" ];
    before = [
      "sysinit.target"
      "shutdown.target"
      "nix-daemon.socket"
      "nix-daemon.service"
    ];
    after = [ "local-fs.target" ];
    conflicts = [ "shutdown.target" ];
    restartIfChanged = false;
    serviceConfig = {
      Type = "oneshot";
      RemainAfterExit = true;
    };
    script = ''
      ${lib.getExe' config.nix.package.out "nix-store"} --load-db < ${registration}
      touch /etc/NIXOS
      ${lib.getExe' config.nix.package.out "nix-env"} -p /nix/var/nix/profiles/system --set /run/current-system
      rm -f ${registration}
    '';
  };

  boot.kernelParams = [
    "console=${if pkgs.stdenv.hostPlatform.isAarch64 then "ttyAMA0" else "ttyS0"}"
    "console=tty0"
  ];
  boot.initrd.availableKernelModules = [
    "virtio_pci"
    "virtio_scsi"
  ];
  virtualisation.virtualbox.guest.enable = true;

  services.xserver.enable = true;
  services.desktopManager.plasma6.enable = true;
  services.displayManager = {
    sddm.enable = true;
    defaultSession = "plasmax11";
    autoLogin = {
      enable = true;
      inherit user;
    };
  };
  networking.networkmanager.enable = true;
  networking.hostName = "iris-richwasm";

  users.users.${user} = {
    isNormalUser = true;
    extraGroups = [
      "wheel"
      "networkmanager"
    ];
    initialPassword = user;
  };
  security.sudo.wheelNeedsPassword = false;

  environment.systemPackages = with pkgs; [
    firefox
    kdePackages.kate
    neovim
    emacs
    nano
    git
    curl
    wget
    unzip
    tree
    python3
  ];

  nix.settings.experimental-features = [
    "nix-command"
    "flakes"
  ];
  nix.registry.nixpkgs.flake = self.inputs.nixpkgs;
  system.extraDependencies = [
    self.devShells.${pkgs.stdenv.hostPlatform.system}.default.inputDerivation
  ]
  ++ lib.attrValues self.inputs;

  systemd.services.copy-iris-richwasm = {
    wantedBy = [ "multi-user.target" ];
    before = [ "display-manager.service" ];
    unitConfig = {
      ConditionPathExists = "!${repo}";
      RequiresMountsFor = source;
    };
    serviceConfig = {
      Type = "oneshot";
      User = user;
    };
    path = [ pkgs.git ];
    script = ''
      cp -r ${source} ${repo}
      chmod -R u+w ${repo}
      cd ${repo}
      git init -q
      git add -A
      git -c user.name=artifact -c user.email=artifact@localhost commit -qm "artifact snapshot"
    '';
  };

  system.stateVersion = "26.05";
}
