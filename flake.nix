{
  description = "Rusholme — a toy Haskell compiler in Zig";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    zig-overlay.url = "github:mitchellh/zig-overlay";
  };

  outputs = { self, nixpkgs, flake-utils, zig-overlay }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs {
          inherit system;
          overlays = [ zig-overlay.overlays.default ];
        };

        isDarwin = pkgs.stdenv.isDarwin;
      in
      {
        devShells.default = pkgs.mkShell {
          name = "rusholme";

          buildInputs = with pkgs; [
            # Compiler toolchain
            zigpkgs.master          # latest Zig nightly (matches 0.16.0-dev)
            llvmPackages_19.llvm    # LLVM for future backend work
            llvmPackages_19.lld     # LLVM linker

            # Development tools
            git
          ] ++ pkgs.lib.optionals (!isDarwin) [
            # Linux-only tools
            valgrind
          ];

          shellHook = ''
            echo "🍛 Rusholme dev environment loaded"
            echo "   Zig:  $(zig version)"
            echo "   LLVM: $(llvm-config --version)"
            echo ""
          '';
        };
      }
    );
}
