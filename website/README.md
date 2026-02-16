# Rusholme Website

A modern, responsive static website for the Rusholme Haskell compiler project, hosted on GitHub Pages.

## Features

- **Hero Section** - Eye-catching introduction with animated gradient orbs and the official logo
- **About Section** - Explains the "Curry Mile" backstory and project goals
- **Pipeline Visualization** - Interactive SVG diagram showing the compilation pipeline
- **Roadmap Section** - Milestone tracking with progress indicators
- **Dynamic Recent Progress** - Built via Node.js script that fetches closed issues from GitHub API
- **Live Documentation** - Client-side rendering of DESIGN.md and ROADMAP.md from GitHub
- **Responsive Design** - Mobile-first with hamburger menu navigation

## Development

### Prerequisites

- Node.js (v18+ recommended)
- npm or yarn

### Installation

```bash
cd website
npm install
```

### Building the Website

The build process fetches the latest GitHub issues and generates the static HTML:

```bash
cd website
npm run build
```

This does the following:
1. Reads `template.html`
2. Fetches recent closed issues from GitHub API
3. Replaces the `<!-- RECENT_ISSUES_PLACEHOLDER -->` with actual data
4. Outputs `index.html` ready for deployment

### Local Preview

```bash
# Using npm serve (recommended)
cd website
npm run serve

# Or with Python
cd website
python -m http.server 8000

# Or with Node.js's http-server
cd website
npx http-server .
```

Then open `http://localhost:8000` in your browser.

### Making Changes

1. **Edit `template.html`** - This is the source template with the placeholder
2. **Run `npm run build`** to generate the final `index.html`
3. **Test locally** with `npm run serve`
4. **Commit both files** (`template.html` and `index.html`)

> **Important:** Always edit `template.html`, not `index.html`. If you edit `index.html` directly, your changes will be overwritten by the next build.

## File Structure

```
website/
├── package.json          # npm config with build/serve scripts
├── build.js             # Build script that fetches GitHub data
├── template.html        # Source template (edit this)
├── index.html           # Generated output (do not edit)
├── official-logo.png    # Official Rusholme logo
├── logo.png             # Legacy/backup logo
└── README.md            # This file
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

- **Logo**: Replace `official-logo.png` with your own
- **Recent Progress**: Run `npm run build` to refresh GitHub data
- **Milestone Progress**: Manually update percentages in the roadmap section HTML
- **Documentation**: Automatically rendered from GitHub - no manual updates needed

## Troubleshooting

### Build fails with "template.html not found"

Make sure you're running from the `website/` directory:

```bash
cd website
npm run build
```

### Recent progress shows old data

Run `npm run build` again to fetch the latest GitHub issues.

### GitHub API rate limit

If you see rate limit errors, you can add a GitHub token. Create a `.env` file:

```bash
GITHUB_TOKEN=your_token_here
```

Then update `build.js` to use `process.env.GITHUB_TOKEN` in the request headers.

## Browser Compatibility

- Chrome/Edge 90+
- Firefox 88+
- Safari 14+
- Mobile browsers (iOS Safari, Chrome Mobile)

## Performance

- Single HTML file (~55KB)
- No JavaScript frameworks
- CDN-delivered libraries with good caching
- Critical CSS inlined
- Lazy-loaded content from GitHub

## License

Same as Rusholme project.
