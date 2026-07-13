---
name: fix-broken-precommit-hook
description: Diagnose and fix a git commit hook (pre-commit, pre-push, etc.) that fails to exec even though the file exists and is executable — usually a stale /nix/store shebang path after a nix store gc.
allowed-tools: Bash
---

# Fix Broken Pre-Commit Hook

## Symptom

`git commit` (or push) fails with:

```
fatal: cannot exec '.git/hooks/pre-commit': No such file or directory
```

...but `ls -la .git/hooks/pre-commit` shows the file exists and is executable.
This message is misleading — git isn't lying about the *hook* file, it's
reporting a failed `exec()`, which usually means the interpreter named in the
hook's shebang line no longer exists on disk.

Common root cause on Nix-based projects: `pre-commit` (https://pre-commit.com)
generated the hook with a shebang pinned to a specific Nix store path (e.g.
`#!/nix/store/<hash>-bash-5.3p9/bin/bash`). If that store path is later
garbage-collected (`nix-collect-garbage`, `nix store gc`), the shebang points
at nothing and every exec of the hook fails.

## Diagnosis

1. Confirm the hook file exists and check for a configured custom hooks path:
   ```bash
   git config --get core.hooksPath
   ls -la .git/hooks/pre-commit
   ```
2. Inspect the shebang line:
   ```bash
   head -5 .git/hooks/pre-commit
   ```
3. Check whether the interpreter path in the shebang actually exists:
   ```bash
   ls <path-from-shebang>
   ```
   If this reports "No such file or directory", that's the root cause —
   the shebang target was gc'd.

## Fix

Regenerate the hook inside the project's Nix dev shell so the new shebang
points at a store path that currently exists:

```bash
nix develop --command pre-commit install --overwrite
```

If this errors with:

```
[ERROR] Cowardly refusing to install hooks with `core.hooksPath` set.
hint: `git config --unset-all core.hooksPath`
```

check what it's set to — `git config --get core.hooksPath`. If it just
points at the default `.git/hooks` (redundant, no functional effect), it's
safe to unset and retry:

```bash
git config --unset-all core.hooksPath
nix develop --command pre-commit install --overwrite
```

`git config` edits are a "confirm with the user first" class of change —
don't run the unset unprompted. If `core.hooksPath` points somewhere
non-default, stop and ask before touching it; something else may depend on
that custom path.

Then retry the commit. If `pre-commit` isn't managing hooks for this repo (no
`.pre-commit-config.yaml`, or a different hook manager), regenerate via
whatever installed the hook originally — but the underlying fix is always
"reinstall the hook from inside the environment that has a live interpreter,"
not to hand-edit the shebang.

## Notes

- Don't delete `.git/hooks/pre-commit` as a shortcut — investigate the
  shebang first; the hook itself is very likely fine.
- Never bypass with `git commit --no-verify` to work around this — that
  skips the checks the hook exists to enforce.
- This class of bug isn't specific to `pre-commit`: any hook (or any script)
  with an absolute Nix store shebang will break the same way after a gc.
