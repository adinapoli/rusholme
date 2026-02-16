# Rusholme Website

A modern, responsive static website for the Rusholme Haskell compiler project, hosted on GitHub Pages.

## Features

- **Hero Section** - Eye-catching introduction with animated gradient orbs and floating logo
- **About Section** - Explains the "Curry Mile" backstory and project goals
- **Pipeline Visualization** - Interactive SVG diagram showing the compilation pipeline
- **Roadmap Section** - Milestone tracking with progress indicators
- **Dynamic Recent Progress** - Fetches closed issues from GitHub API to show recent work
- **Live Documentation** - Renders DESIGN.md and ROADMAP.md previews directly from GitHub
- **Responsive Design** - Mobile-first with hamburger menu navigation
- **Smooth Animations** - Fade-in effects, floating elements, and animated SVG connectors

## Tech Stack

This is a **pure static site** - no build step required:

- **Tailwind CSS** (via CDN) - Utility-first styling
- **Marked.js** (via CDN) - Client-side markdown parsing  
- **Lucide Icons** (via CDN) - Beautiful icon set
- **GitHub API** - Dynamic issue fetching for recent progress section
- **Inter & JetBrains Mono** (Google Fonts) - Typography

## Development

### Local Preview

The simplest way to preview the website locally:

```bash
# Using Python (if installed)
cd website
python -m http.server 8000

# Or using Node.js (if installed)
npx serve .

# Or using PHP (if installed)
php -S localhost:8000
```

Then open `http://localhost:8000` in your browser.

### Direct File Opening

The site can also be opened directly as a file:

```bash
cd website
open index.html  # macOS
xdg-open index.html  # Linux
start index.html  # Windows
```

Note: Some features (like markdown fetching) may be blocked by CORS when opening as a file due to browser security policies. A local server is recommended.

## Deployment

This website is configured for GitHub Pages:

1. The `index.html` is designed to work at the root path
2. All assets are self-contained in the same directory or loaded from CDNs
3. GitHub Actions will automatically build and deploy to `gh-pages` branch

To deploy manually:

```bash
# From the rusholme root
cd website
git checkout --orphan gh-pages
git add index.html logo.png
git commit -m "Deploy website"
git push origin gh-pages
```

The site will be available at: `https://adinapoli.github.io/rusholme/`

## Customization

### Colors

The theme uses a Zig-inspired orange palette:

- `--zig`: #f7a41d
- `--haskell`: #b87e18

These can be modified in the `<style>` section of `index.html`.

### Content Updates

- **Logo**: Replace `logo.png` with your own
- **Recent Progress**: Automatically fetched from GitHub API - no manual updates needed
- **Milestone Progress**: Update the percentages in the roadmap section HTML
- **Documentation**: Automatically rendered from GitHub - no manual updates needed

## Browser Compatibility

- ✅ Chrome/Edge 90+
- ✅ Firefox 88+
- ✅ Safari 14+
- ✅ Mobile browsers (iOS Safari, Chrome Mobile)

## Performance

The site is optimized for speed:
- Single HTML file (~25KB gzipped)
- No JavaScript frameworks overhead
- CDN-delivered libraries with good caching
- Critical CSS inlined
- Lazy-loaded documentation content

## License

Same as Rusholme project.
