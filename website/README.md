# Rusholme Website

A modern, responsive static website for the Rusholme Haskell compiler project, hosted on GitHub Pages.

## Features

- **Hero Section** — Eye-catching introduction with animated gradient orbs and the official logo
- **About Section** — Explains the "Curry Mile" backstory and project goals
- **Pipeline Visualization** — Interactive SVG diagram showing the compilation pipeline
- **Roadmap Section** — Milestone tracking with progress indicators
- **Dynamic Recent Progress** — Built via Node.js script that fetches closed issues from GitHub API
- **Live Documentation** — Client-side rendering of DESIGN.md and ROADMAP.md from GitHub
- **Browser REPL** — Live Haskell evaluation via the WASM-compiled REPL (`repl.wasm`)
- **Responsive Design** — Mobile-first with hamburger menu navigation

## Development

### Quick Start (Nix)

From the repository root:

```bash
# Enter the website dev shell, then run the all-in-one command
nix develop .#website
website-dev
```

`website-dev` will:
1. Build the Zig project (producing `repl.wasm`)
2. Install npm dependencies
3. Run the website build script (copies `repl.wasm`, fetches GitHub data)
4. Serve the website on http://localhost:3000

### Manual Steps

Inside the `nix develop .#website` shell you can also run each step individually:

```bash
zig build                              # build the compiler + repl.wasm
cd website && npm install              # install npm deps (first time only)
npm run build                          # generate index.html, copy repl.wasm
npx serve .                            # serve on http://localhost:3000
```

### Without Nix

Prerequisites: Zig (0.16.0-dev), Node.js (v18+), npm.

```bash
zig build
cd website
npm install
npm run build
npx serve .
```

### Making Changes

1. **Edit `template.html`** — this is the source template with the placeholder
2. **Run `npm run build`** to generate the final `index.html`
3. **Test locally** with `npx serve .`
4. **Commit both files** (`template.html` and `index.html`)

> **Important:** Always edit `template.html`, not `index.html`. The build script
> generates `index.html` from the template — direct edits will be overwritten.

## File Structure

```
website/
├── package.json          # npm config with build/serve scripts
├── build.js              # Build script that fetches GitHub data and copies repl.wasm
├── template.html         # Source template (edit this)
├── index.html            # Generated output (do not edit)
├── official-logo.png     # Official Rusholme logo
├── logo.png              # Legacy/backup logo
└── README.md             # This file
```

## Deployment

The website is automatically deployed to GitHub Pages via GitHub Actions.

## Customization

### Colors

The theme uses a Zig-inspired orange palette:

- `--zig`: #f7a41d
- `--haskell`: #b87e18

Edit the CSS variables in `template.html` to customize.

### Content Updates

- **Logo**: Replace `official-logo.png`
- **Recent Progress**: Run `npm run build` to refresh GitHub data
- **Milestone Progress**: Update percentages in the roadmap section of `template.html`
- **Documentation**: Automatically rendered from GitHub — no manual updates needed

## Troubleshooting

### `repl.wasm` not found

Run `zig build` from the repository root first. The build script copies
`zig-out/bin/repl.wasm` into the website directory.

### Build fails with "template.html not found"

Make sure you're running from the `website/` directory:

```bash
cd website
npm run build
```

### Recent progress shows old data

Run `npm run build` again to fetch the latest GitHub issues.

### GitHub API rate limit

If you see rate limit errors, set a GitHub token:

```bash
GITHUB_TOKEN=your_token_here npm run build
```

## Browser Compatibility

- Chrome/Edge 90+
- Firefox 88+
- Safari 14+
- Mobile browsers (iOS Safari, Chrome Mobile)

## License

Same as Rusholme project.
