# Rusholme — Agent Instructions

You are working on **Rusholme**, a toy Haskell compiler written in Zig.
Read this file in full before doing anything.

## 1. Understand the Project

1. Read `DESIGN.md` — it contains the full architecture, design decisions, mantras, and references.
2. Read `ROADMAP.md` — it tracks all issues by milestone with their status and dependencies.
3. Browse `issues/` — each epic has a subfolder (e.g. `issues/04-haskell-parser/`) containing
   JSON files for individual tasks. Each JSON file has:
   - `title`, `body` — what to do
   - `depends_on` — local IDs of prerequisite tasks
   - `depends_on_github` — GitHub issue numbers of prerequisites
   - `github_issue` — the GitHub issue number
   - `labels`, `milestone` — metadata

## 2. Pick an Issue

1. Open `ROADMAP.md` and find an issue marked :white_circle: (not started).
2. Check that **all its dependencies** are marked :green_circle: (done). Never start an issue
   whose dependencies are incomplete.
3. Prefer issues in earlier milestones (M0 before M1, M1 before M2, etc.).
4. When multiple issues are available, prefer `priority:critical` > `priority:high` > `priority:medium` > `priority:low`.
5. Read the full JSON file in `issues/` for the issue you pick — it contains detailed
   deliverables and design notes.

## 3. Work on the Issue

### Branch

```bash
git checkout main
git pull origin main
git checkout -b llm-agent/issue-<NUMBER>
```

Where `<NUMBER>` is the GitHub issue number (e.g. `llm-agent/issue-17`).

### Build and Test

```bash
# Build
zig build

# Run all tests
zig build test

# Run a specific test (when available)
zig build test -- --test-filter "test name"
```

The project uses a Nix flake for dependencies. If `zig` is not on PATH, use:

```bash
nix develop --command zig build
nix develop --command zig build test
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
- **Don't break existing tests.** Run `zig build test` before committing. If tests fail,
  fix them or understand why before proceeding.
- **Write clear commit messages.** Use the format: `#<NUMBER>: <short description>`.
  Example: `#17: Define SourceSpan and SourcePos types`.
- **No dead code.** Don't leave commented-out code, unused imports, or TODO placeholders
  that aren't part of the deliverable.
- **Errors are structured, not strings.** Use the `Diagnostic` infrastructure (once built)
  for all user-facing errors. Internal assertions can use Zig's `@panic` or `unreachable`.
- **Source spans everywhere.** Every AST/IR node must carry a `SourceSpan`. Don't skip this
  "for now" — it's a project invariant.
- **Document non-obvious decisions.** If you make a design choice not covered by `DESIGN.md`,
  add a brief comment explaining why.
- **Respect the pipeline boundaries.** Each stage (lexer, parser, Core, GRIN, backend) is a
  separate module with a clean interface. Don't reach across boundaries.

### Project Mantras (from DESIGN.md)

1. **Parse everything GHC parses.** Rusholme should eventually accept every Haskell program
   that GHC accepts, even if runtime behaviour differs.
2. **Leverage battle-tested C libraries.** Zig has exceptional C interop — use strong,
   industrial-grade C libraries for hard tasks whenever possible, and source them via Nix.

## 4. Submit for Review

### Commit and Push

```bash
git add -A
git commit -m "#<NUMBER>: <description>"
git push origin llm-agent/issue-<NUMBER>
```

### Open a Pull Request

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

## 5. Status Legend (ROADMAP.md)

| Emoji | Meaning |
|-------|---------|
| :white_circle: | Not started |
| :large_blue_circle: | In progress (being worked on) |
| :yellow_circle: | In review (PR open) |
| :green_circle: | Done (PR merged) |

## 6. Research Issues

Some issues are `type:research` — their deliverable is a written document, not code.

1. Write the recommendation in `docs/decisions/<issue-number>-<slug>.md`.
2. The document should include: options considered, evaluation criteria, recommendation,
   and rationale.
3. Open a PR for the document the same way as code changes.
4. Downstream implementation issues depend on the research decision — they cannot start
   until the research PR is merged.

## 7. Common Pitfalls

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
