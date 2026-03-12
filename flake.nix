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

        # Shared toolchain used by both dev shells
        zigToolchain = with pkgs; [
          zigpkgs.master          # latest Zig nightly (matches 0.16.0-dev)
          llvmPackages_19.llvm    # LLVM for future backend work
          llvmPackages_19.lld     # LLVM linker
        ];

        websiteDevScript = pkgs.writeShellScriptBin "website-dev" ''
          set -euo pipefail
          cd "$(git rev-parse --show-toplevel)"

          echo "Building Rusholme (zig build)..."
          zig build

          echo "Installing website dependencies..."
          cd website
          npm install --silent

          echo "Building website (copies repl.wasm, fetches GitHub data)..."
          npm run build

          echo ""
          echo "Serving website on http://localhost:3000"
          npx serve .
        '';
      in
      {
        devShells = {
          default = pkgs.mkShell {
            name = "rusholme";

            buildInputs = zigToolchain ++ (with pkgs; [
              git
              pre-commit
              wasmtime
              graalvmPackages.graalvm-ce  # GraalVM CE with Sulong for lli JIT
            ]) ++ pkgs.lib.optionals (!isDarwin) [
              pkgs.valgrind
            ];

            shellHook = ''
              echo "🍛 Rusholme dev environment loaded"
              echo "   Zig:      $(zig version)"
              echo "   LLVM:     $(llvm-config --version)"
              echo "   Wasmtime: $(wasmtime --version 2>&1 | head -n1 || echo 'not found')"
              echo "   GraalVM:  $(lli --version 2>&1 | head -n1 || echo 'not found')"
              echo ""
            '';
          };

          website = pkgs.mkShell {
            name = "rusholme-website";

            buildInputs = zigToolchain ++ (with pkgs; [
              nodejs_22
              git
            ]);

            nativeBuildInputs = [ websiteDevScript ];

            shellHook = ''
              echo "🍛 Rusholme website dev environment loaded"
              echo "   Zig:  $(zig version)"
              echo "   Node: $(node --version)"
              echo ""
              echo "Quick start:  website-dev"
              echo "Manual:       zig build && cd website && npm run build && npx serve ."
              echo ""
            '';
          };
        };
      }
    );
}
