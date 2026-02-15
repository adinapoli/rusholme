# Rusholme — Documentation & References

This directory contains reference materials, papers, and notes collected during
the development of the Rusholme compiler.

## Structure

```
docs/
├── README.md              ← you are here
└── references/            ← papers and external references
    ├── grin-overview.md   ← GRIN compiler framework (our core IR choice)
    ├── lambda-ultimate-ssa.md  ← SSA + regions for functional langs
    └── purecake.md        ← verified lazy functional compiler
```

## Adding References

When citing a new paper or web resource during development, add a markdown file
to `references/` with:

1. Title, source URL, authors, date
2. Abstract or summary
3. Relevance to Rusholme
4. Links to PDF / DOI where available
