# Compatibility shim so `nix-shell` works alongside `nix develop`.
# Delegates to the flake's devShell output.
(builtins.getFlake (toString ./.)).devShells.${builtins.currentSystem}.default
