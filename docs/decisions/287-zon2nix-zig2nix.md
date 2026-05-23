# Decision 287: Evaluate `zon2nix` and `zig2nix` for Nix Integration

**Status:** Accepted (adopt `zon2nix`; reject `zig2nix`)
**Date:** 2026-05-23
**Issue:** #287

## Context

Rusholme's reproducible build comes from `flake.nix`, which pins the Zig
toolchain (via `mitchellh/zig-overlay`), LLVM 19, `lld`, `replxx`, and
GraalVM. Zig package dependencies are declared in `build.zig.zon`:
currently just `zig-clap@0.11.0`, plus the project itself.

Today those dependencies live as vendored snapshots under `zig-pkg/` (e.g.
`zig-pkg/clap-0.11.0-…/`). That works but has costs:

- Manual update workflow.
- Inflates the repo (the clap tree is ~50 files).
- The vendored hash is silently authoritative — no chain back to the
  source URL/hash recorded in `build.zig.zon`.

As the dependency set grows (likely candidates: a benchmark library
post-#291, a string library if #293 ever activates one, possible
LSP-related crates), the vendoring strategy will not scale.

[zon2nix]: https://github.com/nix-community/zon2nix
[zig2nix]: https://github.com/Cloudef/zig2nix

## Candidates

### `zon2nix` (nix-community)

- **Scope:** narrow — converts `build.zig.zon` dependencies into a
  generated `deps.nix` derivation.
- **Workflow:** `zon2nix` produces `deps.nix`; the Nix derivation uses
  `postPatch` to symlink the output into Zig's global cache directory,
  satisfying `zig build --system` without internet access.
- **License:** MPL-2.0.
- **Maintainer:** `@figsoda`, under `nix-community`. Active.
- **Regeneration:** manual or via a flake-check / pre-commit hook
  whenever `build.zig.zon` changes.

### `zig2nix` (Cloudef)

- **Scope:** broad — full Zig packaging story: toolchain provisioning,
  dev shells, cross-compilation, binary bundling (incl. AWS Lambda
  packaging), templates, GitHub Actions integration.
- **Includes `zon2nix` functionality:** chains
  `.zon → JSON → lock → Nix` internally as one of several utilities.
- **Toolchain track:** mainline (currently up to 0.16.0 stable, 0.17 dev).
- **License:** MIT.
- **Maintainer:** `@Cloudef`. Active.

## Evaluation

### What we actually need

Just one capability: **`build.zig.zon` → Nix derivation**, hooked into
our existing flake so `nix develop` and `nix build` work without
vendored package directories.

We do *not* need:

- A second toolchain provisioner — `mitchellh/zig-overlay` already pins
  `zigpkgs."0.16.0"` and is the source of truth for the Zig version.
  Replacing it with `zig2nix` would mean re-pinning the toolchain twice
  in the same flake, which is exactly the kind of mismatch we'd want
  to avoid.
- Cross-compilation packaging — Rusholme already builds native and
  wasm32-wasi via plain `zig build`; nothing in the current backend
  story needs `zig2nix`'s bundling.
- AWS Lambda packaging, GitHub Actions templates, etc. — out of scope.

### Comparison

| Property | `zon2nix` | `zig2nix` |
|----------|-----------|-----------|
| Solves the specific need (deps from `.zon`) | Yes | Yes (one of many) |
| Replaces our Zig pin | No | Yes (would conflict with `zig-overlay`) |
| Surface area / coupling | Minimal | Large |
| License | MPL-2.0 | MIT |
| Required when deps change | Re-run on `.zon` edit | Same |

### Risk vs. benefit

- `zon2nix` is the minimum tool that retires the `zig-pkg/` vendoring
  story without taking opinion on the rest of the flake. Failure mode
  is "regenerate `deps.nix`"; nothing else moves.
- `zig2nix` is well-engineered but its breadth is the cost. Adopting it
  means replacing parts of the flake that already work and that are
  shared, ergonomically, with the rest of the Zig-overlay-using
  ecosystem.

## Recommendation

**Adopt `zon2nix`. Reject `zig2nix` (for now).**

The right shape is:

1. Add `zon2nix` as a flake input (or run via `nix run`).
2. Generate `deps.nix` from `build.zig.zon` and commit it.
3. Wire it into `flake.nix` so the `default` dev shell symlinks the
   resulting derivation into Zig's global cache (`postPatch` pattern
   from the `zon2nix` README).
4. Delete the vendored `zig-pkg/clap-0.11.0-…/` tree and replace its
   references with cache-resolved dependencies.
5. Add a pre-commit hook (or a CI check) that re-runs `zon2nix` and
   fails if `deps.nix` is stale vs `build.zig.zon`.

Keep `zig2nix` on the radar. If we ever ship Rusholme as a Nix-packaged
binary (e.g. via a `nix profile install` story for users) and want
cross-compilation packaging out of the box, revisiting `zig2nix` then
is reasonable — but driven by *that* need, not pre-emptively.

## Follow-ups

The implementation is out of scope for the research issue. Concrete
next steps to file as separate issues:

1. Switch from vendored `zig-pkg/clap-…/` to `zon2nix`-resolved
   dependency. Includes the flake wiring, `.gitignore` updates, and a
   CI check for `deps.nix` staleness.
2. Document the dependency-update workflow ("edit `build.zig.zon`, run
   `nix run .#zon2nix-update`, commit `deps.nix`") in `CONTRIBUTING.md`.

## References

- [`zon2nix`][zon2nix] — narrow `.zon` → Nix tool.
- [`zig2nix`][zig2nix] — full Zig-on-Nix toolchain/packaging story.
- `flake.nix` — current dev shell.
- `build.zig.zon` — current single-dep manifest (`zig-clap`).
- `zig-pkg/clap-0.11.0-…/` — current vendored snapshot, to be deleted.
