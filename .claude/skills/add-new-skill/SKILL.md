---
name: add-new-skill
description: Creates the scaffolding for a new project-local Claude Skill
allowed-tools: Read Bash
---

Writing good Claude skills is half art half science, but we can facilitate the user.
Whenever this skill is invoked, manually or otherwise, you should ask the user for the
name of the skill (for example "Rebase conflicting branch") then proceed to create the
scaffolding for a new project-local skill by adding the "slugified" directory name and empty
SKILL.md:

```
${PROJECT_ROOT_DIR}/.claude/skills/rebase-conflicting-branch
```

Then, you should ask the user for a succinct description of what you want the skill to achieve,
and keep asking question until the intent clarifies. Once you are happy with the context you
have gathered, extend the `SKILL.md` file with the correct frontformatter syntax:

```yaml
---
name: the-slugified-skill-name
description: The description you inferred, short and descriptive
allowed-tools: <any subselection of tools you want to pre-approve>
---

<the skill context as you extracted it>
```

Make sure the skill is focused, self-contained and useful, i.e. it's an actionable procedure,
not a collection of facts. If the skill content is big, consider splitting the skill content into
subsequent .md files to be placed in the slugified skill folder, and make sure these are discoverable
in the skill body itself. Example:

```yaml
For the full set of conventions, read `${CLAUDE_SKILL_DIR}/style-guide.md`.
```
