# Rusholme — Agent Instructions

You are working on **Rusholme**, a Haskell compiler written in Zig.
Read this file in full before doing anything.

## 1. Understand the Project

1. Read `DESIGN.md` — it contains the full architecture, design decisions, mantras, and references.
2. Read `ROADMAP.md` — it tracks all issues by milestone with their status and dependencies.

## 2. Preflight Check (before starting any issue)

Before any agent (human or machine) begins work on a new issue, run a consistency
check across the three sources of truth. **Github is the ultimate authority** —
`ROADMAP.md` must agree with it, not the other way around.

### What to check

1. **GitHub issues via `gh`** — for every issue referenced in `ROADMAP.md`, verify:
   - The issue exists on GitHub (`gh issue view <NUMBER>`).
   - Its open/closed state is consistent with the roadmap status
     (:green_circle: = closed, everything else = open).
   - Its title matches (minor wording differences are acceptable).

2. **Cross-check** — flag any issue that:
   - Appears on GitHub but not in `ROADMAP.md` (orphaned issue).
   - Has dependency or status mismatches between the three sources.

### If inconsistencies are found

Do **not** start the new issue. Instead, ensure consistency is regained. What it might
happen is that issues in the ROADMAP as still "in review" because the relevant PR is still
open. However, if any issue in the ROADMAP is marked as "in review" but you spot that the relevant
PR has been merged, then change the status in the roadmap to be "DONE".

Remember: A closed or merged issue on Github is synonym with DONE, modulo exceptional cases we
can disragard here.

Finally:

```bash
git checkout project-planning
git rebase main
# Fix ROADMAP.md, and/or GitHub issue state to restore consistency.
git add -A
git commit -m "sync: Reconcile ROADMAP with GitHub state"
git push origin project-planning
# Open a PR for the sync, get it merged, then proceed with the original issue.
```

### If everything is consistent

Proceed to "Pick an Issue" below.

## 3. Pick an Issue

1. Open `ROADMAP.md` and find an issue marked :white_circle: (not started).
2. Check that **all its dependencies** are marked :green_circle: (done). Never start an issue
   whose dependencies are incomplete.
3. Prefer issues in earlier milestones (M0 before M1, M1 before M2, etc.).
4. When multiple issues are available, prefer `priority:critical` > `priority:high` > `priority:medium` > `priority:low`.
5. Read the full issue on Github, as it contains deliverables and design notes.

## 4. Work on the Issue

IMPORTANT: This is a zig project created primarily with the goal of learning Zig, so it's important that:

1. The code is as idiomatic as possible;
2. The code respects principles of good software engineering (abstraction, information hiding, encapsulation);
3. The code would use Zig's ecosystem best practices (de facto libraries, etc).

Every time you write a single line of code, respect the three laws above.

### Project Philosophy: Production Craft, Research Spirit

Rusholme calls itself a "toy" compiler in the sense that it targets a subset of
Haskell and is not yet production-deployed. **Do not let that word lower your
standards.** The codebase is built to last — it may grow into a serious compiler
over time, and early architectural shortcuts compound into permanent constraints.
Every design decision should be made as if it will still be in the codebase in
five years, because it might be.

Concretely, this means:

- **Code as if it will be maintained for years.** Clean module boundaries, no
  leaking abstractions, no "we'll fix this later" shortcuts that embed
  themselves into the IR or the calling convention.
- **Algorithm choices should be principled, not just expedient.** If a
  well-studied algorithm from the literature fits, use it and cite the paper.
  "Good enough for a toy" is not a valid reason to pick a weaker design.
- **Be research-forward.** When there are multiple valid approaches, prefer the
  more modern or theoretically interesting one — as long as it doesn't add
  runaway complexity. This project is also a learning exercise in compiler
  construction; exploring ideas like bidirectional typechecking, GRIN, or
  ASAP-style deallocation is a feature, not a distraction.
- **"Toy scope" applies to features, not to quality.** We may implement only a
  subset of Haskell 2010 — that is a scope decision. Within that scope, the
  implementation should be correct, well-tested, and well-structured. A small
  compiler that works perfectly is far more valuable than a large one that
  almost works.
- **Do not defer correctness.** Source spans on every node, zero memory leaks,
  structured diagnostics — these are not polish to add later. They are load-
  bearing properties that everything downstream depends on.

### Branch for Project Planning

For tasks involving issue synchronization, roadmap updates, or general project planning:

```bash
git checkout project-planning
git rebase main
# Perform planning work...
git push origin project-planning
```

Always ensure the `project-planning` branch is up-to-date with `main` before starting.

### Build and Test

```bash
# Build
zig build

# Run all tests
zig build test --summary all

# Run a specific test (when available)
zig build test -- --test-filter "test name"
```

The project uses a Nix flake for dependencies. If `zig` is not on PATH, use:

```bash
nix develop --command zig build
nix develop --command zig build test --summary all
```

### Coding Standards

- **Read before writing.** Always read existing code before modifying or adding to it.
  Understand the patterns already in use.
- **Follow existing conventions.** Match the style, naming, and structure of surrounding code.
  If the project uses `snake_case`, use `snake_case`. If it uses `const` for immutable values, do the same.
- **Every deliverable needs tests.** If the issue says "unit tests", write them. Use Zig's
  built-in `test` blocks in the same file or a dedicated test file as appropriate.
- **Keep changes focused.** Only change what the issue asks for. Don't refactor unrelated code,
  add features not requested, or "improve" things outside scope.
- **Don't break existing tests.** Run `zig build test --summary all` before committing. If tests fail,
  fix them or understand why before proceeding.
- **Write clear commit messages.** Use the format: `#<NUMBER>: <short description>`.
  Example: `#17: Define SourceSpan and SourcePos types`.
- **No dead code.** Don't leave commented-out code, unused imports, or TODO placeholders
  that aren't part of the deliverable.
- **Zero leaks.** Every test MUST use `std.testing.allocator` (or `ArenaAllocator`
  wrapping it). Every allocation needs a corresponding `defer` free/deinit. Use
  `errdefer` for error path cleanup. See `CONTRIBUTING.md` for the full policy.
- **Errors are structured, not strings.** Use the `Diagnostic` infrastructure (once built)
  for all user-facing errors. Internal assertions can use Zig's `@panic` or `unreachable`.
- **Source spans everywhere.** Every AST/IR node must carry a `SourceSpan`. Don't skip this
  "for now" — it's a project invariant.
- **Document non-obvious decisions.** If you make a design choice not covered by `DESIGN.md`,
  add a brief comment explaining why.
- **Respect the pipeline boundaries.** Each stage (lexer, parser, Core, GRIN, backend) is a
  separate module with a clean interface. Don't reach across boundaries.
- **Never use the acronym "ICE".** This acronym has negative connotations. Use 
  "internal compiler error" or "compiler bug" instead.

### Project Mantras (from DESIGN.md)

1. **Parse everything GHC parses.** Rusholme should eventually accept every Haskell program
   that GHC accepts, even if runtime behaviour differs.
2. **Leverage battle-tested C libraries.** Zig has exceptional C interop — use strong,
   industrial-grade C libraries for hard tasks whenever possible, and source them via Nix.

## 5. File Follow-up Issues for Known Shortcomings

Before opening the PR, identify any deliberate shortcuts, interim designs, or
known limitations introduced by the implementation. **Every shortcoming must
become a GitHub issue** — do not leave it as a comment, a TODO, or a PR
footnote that will be forgotten.

### What counts as a shortcoming

- An interim design that must change once a later issue is implemented
  (e.g. "keyed on string until the renamer lands").
- A missing invariant that the current code does not enforce but should.
- A piece of functionality explicitly deferred from the issue scope.
- Any place where you wrote "future refactor" or "known limitation" in a comment.

### How to file them

For each shortcoming:

```bash
# Store body in a temp file to avoid shell interpolation issues.
cat > /tmp/issue-body.md << 'EOF'
## Context
<why this shortcoming exists — reference the PR/issue that introduced it>

## Shortcoming
<what is wrong or incomplete>

## Deliverable
<concrete steps to fix it, including which future issue it depends on>

## References
<relevant files, functions, design docs>
EOF

gh issue create \
  --title "<short imperative description>" \
  --body-file /tmp/issue-body.md \
  --label "component:<X>,priority:<Y>,type:feature"
```

Then add the new issue number(s) to `ROADMAP.md` under the appropriate epic,
with the correct dependency links, on the `project-planning` branch.

### When to skip

The only acceptable reason to skip filing a follow-up issue is if the shortcoming
is already tracked by an existing open issue. In that case, add a cross-reference
comment in the code pointing to that issue number.

## 6. Refresh Benchmarks (before opening a PR)

Rusholme tracks its end-to-end performance against GHC over time. The
benchmark suite lives in `bench/`, the results live in
`bench/results.json`, and the website at `/bench/` renders the
JSON as Vega-Lite time-series charts. **Every PR that could plausibly
move performance** (compiler, GRIN, backend, RTS, Prelude) must
re-run the suite locally and commit a fresh entry.

### What "plausibly moves performance" means

Run the benchmarks if your change touches any of:

- `src/backend/`, `src/grin/`, `src/core/`, `src/typecheck/`,
  `src/desugar/`, `src/parser/`, `src/modules/`
- `src/rts/`, `lib/Prelude.hs`, `lib/rhc-prim/`, `lib/ghc-internal/`,
  `lib/base/`
- `bench/` itself (a new bench program counts)

Skip the benchmarks (and explain why in the PR) when your change is
documentation-only, test-only, or strictly mechanical (renames, comment
fixes, ROADMAP updates).

### When to run

Bench **before opening the PR**, not after merging — by the time it is
on `main` a regression is part of the history and must be diagnosed
under a second changeset.  Per-PR is fine when several PRs in a stack
each shift perf in different directions; one bench refresh on the tip
of the stack misses the per-step attribution.  If a stack is shipping
intentionally with one bench commit at the end, say so explicitly in
the cover PR description so reviewers know to attribute the delta to
the whole stack.

### Compare against the previous entry

After `bench-all.sh` writes a new entry, diff the per-program means
against the previous one.  A compact comparison from the repo root:

```bash
python3 - <<'PY'
import json
with open('bench/results.json') as f:
    runs = json.load(f)['runs']
prev, curr = runs[-2]['programs'], runs[-1]['programs']
print(f'{"program":<22}{"prev":>10}{"curr":>10}{"delta":>10}')
for p in sorted(curr):
    pv = prev.get(p, {}).get('rhc_mean_ms')
    cv = curr[p]['rhc_mean_ms']
    d  = (cv - pv) / pv * 100 if pv else 0
    if pv:
        print(f'{p:<22}{pv:>10.3f}{cv:>10.3f}{d:>+9.1f}%')
PY
```

**Treat as a regression and chase before pushing**:

- Any program ≥10 ms with a per-program **delta > +10 %**.
- More than three programs with **delta > +20 %** (broad regression).

Programs under ~1 ms run within hyperfine's noise floor — a single-
program +30 % on a sub-millisecond program is usually noise, but five
of them in the same direction is the same broad regression as one
+10 % on a long-running program.  Use the long-running programs
(queens, hanoi, nbody_simple, matmul, knucleotide, fib_rec) as the
primary signal; treat short ones as a corroborating bulk metric.

If the regression is real and intentional (e.g. correctness fix that
trades cycles for soundness), document it in the PR body with the
delta table above and call out which programs slowed by how much.
Reviewers can then decide whether the trade is worth it instead of
discovering it weeks later.

### How to run

From the repo root, with the dev shell active and `ghc` on `PATH`:

```bash
nix develop --command bash -c '
  export PATH="$HOME/.ghcup/bin:$PATH"
  zig build
  ./scripts/bench-all.sh -n 7 -w 3
'
```

`bench-all.sh`:

1. Builds every `bench/*.hs` three times: `rhc -O2` (arena RTS),
   `rhc -O2 --rts=immix` (Immix RTS), and `ghc -O2`.
2. Diff-checks all three binaries' stdouts against the GHC reference
   (aborts on divergence — that's a correctness regression, not a
   perf one, and must be fixed before any timing run is meaningful).
3. Times all three under `hyperfine` (7 runs, 3 warmups by default).
4. Appends a new entry to `bench/results.json` with the current
   commit SHA, host CPU model, GHC version, and per-program mean +
   standard deviation in milliseconds.

### Review and commit

- Read the diff of `bench/results.json` before committing. A surprise
  regression that lines up with your changes is a real signal — chase
  it before opening the PR.
- Stage and commit the JSON alongside the rest of the work:

```bash
git add bench/results.json
git commit -m "#<NUMBER>: refresh bench results"
```

- The website re-renders on every push to `main` and picks up the
  new data points automatically — no extra deploy step.

### Adding a new benchmark

- Drop a `.hs` file into `bench/` whose `main` writes a single line
  to stdout.
- Add a row to `bench/README.md` describing the perf surface the
  program exercises.
- Re-run `bench-all.sh` so the new program appears in
  `bench/results.json` from day one.

## 7. Submit for Review

### Commit and Push

```bash
git add -A
git commit -m "#<NUMBER>: <description>"
git push origin llm-agent/issue-<NUMBER>
```

### Open a Pull Request

Important: when using `gh` to open a PR, sometimes there are problems with character
interpolation in bash. Store the body of the PR in a temporary file, and then slurp that
into `gh`.

```bash
gh pr create \
  --title "#<NUMBER>: <issue title>" \
  --body "Closes #<NUMBER>

## Summary
<brief description of what was implemented>

## Deliverables
- [ ] <checklist from the issue body>

## Testing
<how to verify the changes work>" \
  --base main \
  --head llm-agent/issue-<NUMBER> \
  --reviewer adinapoli
```

### Update the Roadmap

In `ROADMAP.md`, change the issue's status:
- :white_circle: → :yellow_circle: when a PR is open and awaiting review
- :yellow_circle: → :green_circle: when the PR is merged (the reviewer will typically do this)

Commit the roadmap update on the same branch:

```bash
git add ROADMAP.md
git commit -m "#<NUMBER>: Update roadmap status to in-review"
git push origin llm-agent/issue-<NUMBER>
```

## 8. Status Legend (ROADMAP.md)

| Emoji | Meaning |
|-------|---------|
| :white_circle: | Not started |
| :large_blue_circle: | In progress (being worked on) |
| :yellow_circle: | In review (PR open) |
| :green_circle: | Done (PR merged) |

## 9. Research Issues

Some issues are `type:research` — their deliverable is a written document, not code.

1. Write the recommendation in `docs/decisions/<issue-number>-<slug>.md`.
2. The document should include: options considered, evaluation criteria, recommendation,
   and rationale.
3. Open a PR for the document the same way as code changes.
4. Downstream implementation issues depend on the research decision — they cannot start
   until the research PR is merged.

## 10. Common Pitfalls

- **Verify that issue deliverables are architecturally coherent before writing
  any code.** GitHub issues are written by humans (and LLMs) and can contain
  framing errors — terminology borrowed from the wrong model, deliverables that
  contradict the design, or references to the wrong literature. An issue
  description is a *proposal*, not a specification.

  Before starting implementation, cross-check the deliverable against
  `DESIGN.md` and the relevant `docs/` files. If the issue says "implement X"
  but `DESIGN.md` says the project uses a different model that makes X
  meaningless or wrong, **do not implement X**. Instead:
  1. Note the contradiction in a comment on the issue.
  2. Update the issue description with the correct framing.
  3. Then implement what the architecture actually requires.

  Concrete example: issue #384 described thunk evaluation in STG terms ("code
  pointer and environment", "call the thunk code"). Rusholme uses GRIN, where
  thunk forcing is static dispatch on a node tag — there is no `fn_ptr` field.
  An agent that read only the issue text produced an STG runtime; an agent that
  cross-checked `docs/rts-design.md` would have caught the mismatch immediately.

  **The design documents outrank the issue text. Always.**

- **Don't take "kitchen sink" shortcuts for deferred features.** When a AST node or
  expression type cannot be fully implemented yet, do **not** group it into a catch-all
  `ListComp, RecordCon, RecordUpdate =>` block that returns a generic `<unsupported>` placeholder.
  This hides the deferred work with no traceability.

  Instead, each unimplemented case must:
  1. Be handled explicitly in the switch
  2. Include a comment referencing the GitHub issue tracking it (e.g. `// tracked in: https://github.com/.../issues/307`)
  3. If no tracking issue exists, file one before submitting the PR
  4. File a follow-up issue during PR preparation (see section 5)

  The pattern should be:
  ```zig
  // ── Not yet implemented ─────────────────────────────────────────
  //
  // IMPORTANT: Each unsupported case MUST have a tracking issue...
  .ListComp => {
      // tracked in: https://github.com/adinapoli/rusholme/issues/XXX
      return ...
  },
  ```

  This ensures deferred work is discoverable via grep, visible in code review, and
  never forgotten. See issue #307 for the consequence of violating this rule.

- **Don't start an issue with unmet dependencies.** The dependency graph exists for a reason.
  Check `depends_on_github` in the JSON file.
- **Don't modify `DESIGN.md` without discussion.** It's the project's source of truth.
  If you think a design decision needs changing, note it in the PR description.
- **Don't add GHC extensions.** Rusholme targets Haskell 2010. Don't add support for
  GHC-specific syntax or extensions unless an issue explicitly asks for it.
- **Don't optimise prematurely.** Correctness first, performance later. Especially true
  for the interpreter and early pipeline stages.
- **Don't skip the pretty-printer.** Every IR (AST, Core, GRIN) needs a pretty-printer
  for debugging and golden tests. These are not optional.
- **Don't hardcode paths or platform assumptions.** Use Zig's cross-platform APIs.
  The project should build on Linux, macOS, and (eventually) Windows.
