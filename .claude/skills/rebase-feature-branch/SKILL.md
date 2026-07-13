---
name: rebase-feature-branch
description: Rebase the current feature branch onto an updated main after an earlier stacked/standalone PR merged, resolving conflicts and validating before force-pushing.
allowed-tools: Bash, Read, Edit
---

# Rebase Feature Branch onto main

## When to use

An LLM-authored feature branch (with an open PR) has developed conflicts
because an earlier PR — reviewed and merged by Alfredo — touched overlapping
code. This skill brings the branch up to date, resolves conflicts, validates
the result, and pushes.

Scope: **one branch per invocation.** If several PRs are stacked, run this
once per branch, oldest-to-newest, after each merge — don't try to walk the
whole stack in one shot.

## Procedure

1. **Check for uncommitted work** on the current branch before touching
   anything:
   ```bash
   git status --short
   ```
   If dirty, stash (`git stash push -u`) or ask the user how to proceed —
   never discard.

2. **Update main:**
   ```bash
   git checkout main
   git fetch origin
   git pull --rebase origin main
   ```

3. **Rebase the feature branch:**
   ```bash
   git checkout <feature-branch>
   git rebase main
   ```
   Use plain `git rebase main`, not `-i` — this runs unattended, no editor.

4. **On conflicts:** don't blind-accept `--ours`/`--theirs`. For each
   conflicted file:
   - Read both sides of the conflict and understand what each hunk is trying
     to do (the merged-in change vs. this branch's change).
   - Hand-resolve so both pieces of intent survive — e.g. if main renamed a
     function this branch also calls, update the call site rather than
     reverting the rename.
   - `git add <file>` per resolved file, then `git rebase --continue`.
   - If a conflict is genuinely ambiguous (can't tell what one side intended,
     or resolving it requires a product decision), stop and ask the user
     rather than guessing.

5. **Validate before pushing:**
   If you are inside a nix shell already:
   ```bash
   zig build
   zig build test --summary all
   ```
   If you are not:
   ```bash
   nix-shell --run "zig build"
   nix-shell --run "zig build test --summary all"
   ```
   If either fails, **do not push.** Leave the rebase applied locally, report
   the failing build/tests to the user, and let them decide whether to fix,
   take over, or `git rebase --abort`.

6. **Push if green:**
   ```bash
   git push <feature-branch> --force-with-lease
   ```
   Always `--force-with-lease`, never plain `--force` — this branch has an
   open PR someone may have pushed to since you last fetched it.

## Notes

- Never rebase `main` itself onto anything, and never force-push `main`.
- If `git rebase main` reports "up to date" or fast-forwards with zero
  conflicts, still run validation before pushing — a clean rebase can still
  break if main's merged change altered behavior this branch depends on.
- Reference this repo's `CLAUDE.md` for the canonical build/test commands if
  they've changed since this skill was written.
