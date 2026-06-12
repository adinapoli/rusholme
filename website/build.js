#!/usr/bin/env node

/**
 * Rusholme Website Build Script
 * 
 * Generates a static HTML file by replacing the placeholder
 * in template.html with data fetched from GitHub API.
 */

import fs from 'fs';
import path from 'path';
import https from 'https';
import { fileURLToPath } from 'url';

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);

const CONFIG = {
  repoOwner: 'adinapoli',
  repoName: 'rusholme',
  apiBaseUrl: 'https://api.github.com/repos/adinapoli/rusholme',
  maxRecentIssues: 6
};

// Copy logo from assets directory
function copyLogo() {
  const logoSource = path.join(__dirname, '../assets/logo.png');
  const logoTarget = path.join(__dirname, 'logo.png');
  
  if (fs.existsSync(logoSource)) {
    fs.copyFileSync(logoSource, logoTarget);
    console.log('   ✓ Copied logo from assets/');
  } else {
    console.warn('   ⚠️  assets/logo.png not found');
  }
}

// Copy repl.wasm from zig build output to website root
function copyReplWasm() {
  const wasmSource = path.join(__dirname, '../zig-out/bin/repl.wasm');
  const target = path.join(__dirname, 'repl.wasm');

  if (!fs.existsSync(wasmSource)) {
    console.warn('   ⚠️  zig-out/bin/repl.wasm not found — run "zig build" first');
    return;
  }

  fs.copyFileSync(wasmSource, target);
  console.log('   ✓ Copied repl.wasm from zig-out/bin/');
}

// Fetch JSON from URL
function fetchJSON(url) {
  return new Promise((resolve, reject) => {
    https.get(url, {
      headers: { 'User-Agent': 'rusholme-website-build-script' }
    }, (res) => {
      let data = '';
      res.on('data', chunk => data += chunk);
      res.on('end', () => {
        if (res.statusCode >= 200 && res.statusCode < 300) {
          try {
            resolve(JSON.parse(data));
          } catch (e) {
            reject(new Error(`JSON parse error: ${e.message}`));
          }
        } else {
          reject(new Error(`HTTP ${res.statusCode}`));
        }
      });
    }).on('error', reject);
  });
}

// Format time ago
function getTimeAgo(date) {
  const seconds = Math.floor((new Date() - date) / 1000);
  const interval = [
    { s: 31536000, unit: 'year' },
    { s: 2592000, unit: 'month' },
    { s: 86400, unit: 'day' },
    { s: 3600, unit: 'hour' },
    { s: 60, unit: 'minute' }
  ].find(i => Math.floor(seconds / i.s) >= 1);
  
  if (!interval) return 'just now';
  const count = Math.floor(seconds / interval.s);
  return `${count} ${interval.unit}${count > 1 ? 's' : ''} ago`;
}

// Escape HTML
function escapeHtml(text) {
  return text.replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;').replace(/"/g, '&quot;');
}

// Milestone metadata (order, emoji, label)
const MILESTONES = [
  { id: 'M0', emoji: '🚀', label: 'Infrastructure' },
  { id: 'M1', emoji: '👋', label: 'Hello World' },
  { id: 'M2', emoji: '📋', label: 'Basic Programs' },
  { id: 'M3', emoji: '⚙️', label: 'Optimisations' },
  { id: 'M4', emoji: '✨', label: 'Polish' },
];

// Parse ROADMAP.md and compute milestone progress
function computeMilestoneProgress() {
  const roadmapPath = path.join(__dirname, '..', 'ROADMAP.md');
  if (!fs.existsSync(roadmapPath)) {
    console.warn('   ⚠️  ROADMAP.md not found, using fallback');
    return MILESTONES.map(m => ({ ...m, done: 0, total: 0, percentage: 0 }));
  }

  const content = fs.readFileSync(roadmapPath, 'utf-8');
  const lines = content.split('\n');

  // Split lines into milestone sections keyed by "M0", "M1", etc.
  const sections = new Map();
  let currentMilestone = null;

  for (const line of lines) {
    const headingMatch = line.match(/^## (M\d):/);
    if (headingMatch) {
      currentMilestone = headingMatch[1];
      sections.set(currentMilestone, []);
      continue;
    }
    // Stop collecting when we hit the dependency graph or a non-milestone section
    if (line.startsWith('## Dependency Graph') || line.startsWith('## Legend')) {
      currentMilestone = null;
      continue;
    }
    if (currentMilestone) {
      sections.get(currentMilestone).push(line);
    }
  }

  return MILESTONES.map(m => {
    const sectionLines = sections.get(m.id) || [];
    let done = 0;
    let total = 0;

    for (const line of sectionLines) {
      // Match table rows that contain a status emoji
      // Format: | [#N](url) | title | deps | :emoji: |
      if (line.includes(':green_circle:')) { done++; total++; }
      else if (line.includes(':yellow_circle:')) { total++; }
      else if (line.includes(':large_blue_circle:')) { total++; }
      else if (line.includes(':white_circle:')) { total++; }
    }

    const percentage = total > 0 ? Math.round((done / total) * 100) : 0;
    return { ...m, done, total, percentage };
  });
}

// Generate milestone cards HTML
function generateMilestoneCardsHTML(milestones) {
  return milestones.map(m => {
    let statusIcon, statusText, statusColor, barGradient, opacity;

    if (m.percentage === 100) {
      statusIcon = '<i data-lucide="check-circle-2" class="w-4 h-4"></i>';
      statusText = '100% complete';
      statusColor = 'text-green-500';
      barGradient = 'bg-gradient-to-r from-green-500 to-emerald-500';
      opacity = '';
    } else if (m.percentage > 0) {
      statusIcon = '<i data-lucide="clock" class="w-4 h-4"></i>';
      statusText = `~${m.percentage}% complete`;
      statusColor = 'text-blue-500';
      barGradient = 'bg-gradient-to-r from-blue-500 to-indigo-500';
      opacity = '';
    } else {
      statusIcon = '<i data-lucide="circle" class="w-4 h-4"></i>';
      statusText = 'Not started';
      statusColor = 'text-gray-500';
      barGradient = 'bg-gray-700';
      opacity = ' opacity-60';
    }

    return `                <div class="card-hover p-6 bg-gray-900 rounded-2xl border border-gray-800${opacity}">
                    <div class="text-4xl mb-4">${m.emoji}</div>
                    <h3 class="font-bold text-lg text-white mb-1">${m.id}</h3>
                    <p class="text-sm text-gray-500 mb-4">${escapeHtml(m.label)}</p>
                    <div class="flex items-center gap-2 text-sm ${statusColor} font-semibold">
                        ${statusIcon}
                        ${statusText}
                    </div>
                    <div class="mt-4 h-2 bg-gray-800 rounded-full overflow-hidden">
                        <div class="h-full ${barGradient} progress-bar" style="width: ${m.percentage}%"></div>
                    </div>
                </div>`;
  }).join('\n\n');
}

// Fetch recent issues from GitHub API
async function fetchRecentIssues() {
  try {
    const issues = await fetchJSON(
      `${CONFIG.apiBaseUrl}/issues?state=closed&per_page=20&sort=closed&direction=desc`
    );
    return issues
      .filter(i => !i.pull_request)
      .slice(0, CONFIG.maxRecentIssues)
      .map(issue => ({
        number: issue.number,
        title: issue.title,
        url: issue.html_url,
        timeAgo: getTimeAgo(new Date(issue.closed_at))
      }));
  } catch (error) {
    console.warn(`GitHub API error: ${error.message}`);
    console.log('Using fallback content...');
    return [];
  }
}

// Generate recent progress HTML
function generateRecentProgressHTML(issues) {
  if (issues.length === 0) {
    return `<div class="flex items-start gap-3">
        <div class="w-6 h-6 rounded-full bg-green-500/20 flex items-center justify-center flex-shrink-0 mt-0.5">
          <svg width="12" height="12" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="3">
            <polyline points="20 6 9 17 4 12"></polyline>
          </svg>
        </div>
        <div>
          <a href="https://github.com/adinapoli/rusholme/issues" target="_blank" class="text-white hover:text-[#f7a41d] font-medium">
            View all recent progress on GitHub
          </a>
          <p class="text-xs text-gray-500 mt-1">Issues are dynamically loaded via GitHub API</p>
        </div>
      </div>`;
  }
  
  return issues.map(issue => `<div class="flex items-start gap-3">
      <div class="w-6 h-6 rounded-full bg-green-500/20 flex items-center justify-center flex-shrink-0 mt-0.5">
        <svg width="12" height="12" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="3">
          <polyline points="20 6 9 17 4 12"></polyline>
        </svg>
      </div>
      <div class="flex-1">
        <a href="${issue.url}" target="_blank" class="text-white hover:text-[#f7a41d] font-medium">
          #${issue.number}: ${escapeHtml(issue.title)}
        </a>
        <p class="text-xs text-gray-500 mt-1">Closed ${issue.timeAgo}</p>
      </div>
    </div>`).join('');
}

// ── Benchmark section ─────────────────────────────────────────────────

/**
 * Read the checked-in bench/results.json (committed by hand after
 * `scripts/bench-all.sh` runs locally). Returns null when the file
 * is missing so build can still complete on branches that pre-date
 * the bench scaffold.
 */
function loadBenchResults() {
  const benchPath = path.join(__dirname, '../bench/results.json');
  if (!fs.existsSync(benchPath)) return null;
  try {
    const data = JSON.parse(fs.readFileSync(benchPath, 'utf-8'));
    if (!data.runs || data.runs.length === 0) return null;
    return data;
  } catch (err) {
    console.warn(`   ⚠️  Failed to parse bench/results.json: ${err.message}`);
    return null;
  }
}

/**
 * One Vega-Lite chart per program, wrapped in an interactive
 * explorer: a program list on the left (one row per benchmark,
 * tinted green when the best rhc backend beats GHC in the latest
 * run, red-ish when it trails), and the selected program's
 * time-series chart on the right. Charts show rhc vs ghc mean
 * execution time over time with a shaded ±σ band; they are
 * rendered lazily by vega-embed on first selection and cached.
 *
 * Specs are emitted inline and rendered client-side by vega-embed.
 */
function generateBenchExplorerHTML(bench) {
  // Collect every (date, program, compiler, ms) tuple across all runs.
  // Also pre-compute the stddev band edges so Vega-Lite doesn't need
  // a calculate transform.
  const records = [];
  for (const run of bench.runs) {
    for (const [name, p] of Object.entries(run.programs)) {
      records.push({
        program: name, date: run.date, compiler: 'rhc (arena)',
        mean_ms: p.rhc_mean_ms,
        lo_ms: Math.max(0.001, p.rhc_mean_ms - p.rhc_stddev_ms),
        hi_ms: p.rhc_mean_ms + p.rhc_stddev_ms,
        stddev_ms: p.rhc_stddev_ms, commit: run.commit,
      });
      // The immix series is only recorded by post-#798 runs. Older
      // entries skip it; older charts simply lack that line.
      if (typeof p.rhc_immix_mean_ms === 'number') {
        records.push({
          program: name, date: run.date, compiler: 'rhc (immix)',
          mean_ms: p.rhc_immix_mean_ms,
          lo_ms: Math.max(0.001, p.rhc_immix_mean_ms - p.rhc_immix_stddev_ms),
          hi_ms: p.rhc_immix_mean_ms + p.rhc_immix_stddev_ms,
          stddev_ms: p.rhc_immix_stddev_ms, commit: run.commit,
        });
      }
      records.push({
        program: name, date: run.date, compiler: 'ghc',
        mean_ms: p.ghc_mean_ms,
        lo_ms: Math.max(0.001, p.ghc_mean_ms - p.ghc_stddev_ms),
        hi_ms: p.ghc_mean_ms + p.ghc_stddev_ms,
        stddev_ms: p.ghc_stddev_ms, commit: run.commit,
      });
    }
  }
  const names = Array.from(new Set(records.map(r => r.program))).sort();

  const latest = bench.runs[bench.runs.length - 1];
  const previous = bench.runs.length > 1 ? bench.runs[bench.runs.length - 2] : null;
  const specs = {};
  const rowsMeta = [];

  // Gap = best rhc backend / ghc, both from the same run. < 1 means
  // rusholme wins.
  const gapIn = (run, name) => {
    const p = run && run.programs[name];
    if (!p) return null;
    const rhcBest = (typeof p.rhc_immix_mean_ms === 'number')
      ? Math.min(p.rhc_mean_ms, p.rhc_immix_mean_ms)
      : p.rhc_mean_ms;
    return rhcBest / p.ghc_mean_ms;
  };

  for (const name of names) {
    const data = records.filter(r => r.program === name);
    const spec = {
      $schema: 'https://vega.github.io/schema/vega-lite/v5.json',
      background: 'transparent',
      width: 'container',
      height: 280,
      padding: { left: 12, right: 12, top: 12, bottom: 24 },
      data: { values: data },
      encoding: {
        x: {
          field: 'date', type: 'temporal',
          axis: { title: null, format: '%b %d', tickCount: 6, labelColor: '#9ca3af', tickColor: '#374151', domainColor: '#374151' },
        },
        color: {
          field: 'compiler', type: 'nominal',
          scale: {
            domain: ['rhc (arena)', 'rhc (immix)', 'ghc'],
            range: ['#34d399', '#60a5fa', '#f7a41d'],
          },
          legend: { labelColor: '#d1d5db', titleColor: '#9ca3af', orient: 'top-right', symbolType: 'circle' },
        },
      },
      layer: [
        // ±σ band — Vega-Lite renders this as a vertical rule per
        // sample, so a single run already shows something useful
        // (a coloured tick on each compiler's mean).
        {
          mark: { type: 'rule', strokeWidth: 6, opacity: 0.18, strokeCap: 'round' },
          encoding: {
            y:  { field: 'lo_ms', type: 'quantitative', scale: { type: 'log' }, axis: null },
            y2: { field: 'hi_ms' },
          },
        },
        // Mean — both the connecting line (for multi-run histories)
        // and the marker dots (so a 1-sample history is not blank).
        {
          mark: { type: 'line', strokeWidth: 2.5, interpolate: 'monotone' },
          encoding: {
            y: {
              field: 'mean_ms', type: 'quantitative',
              scale: { type: 'log', nice: true, zero: false },
              axis: { title: 'mean (ms, log)', titleColor: '#9ca3af', labelColor: '#9ca3af', tickColor: '#374151', domainColor: '#374151', gridColor: '#1f2937' },
            },
          },
        },
        {
          mark: { type: 'point', filled: true, size: 80, opacity: 1 },
          encoding: {
            y: { field: 'mean_ms', type: 'quantitative', scale: { type: 'log' }, axis: null },
            tooltip: [
              { field: 'compiler', type: 'nominal', title: 'compiler' },
              { field: 'mean_ms', type: 'quantitative', title: 'mean (ms)', format: '.3f' },
              { field: 'stddev_ms', type: 'quantitative', title: 'σ (ms)', format: '.3f' },
              { field: 'date', type: 'temporal', title: 'when' },
              { field: 'commit', type: 'nominal', title: 'commit' },
            ],
          },
        },
      ],
      config: {
        view: { stroke: 'transparent' },
        axis: { grid: true, gridColor: '#1f2937', labelFont: 'ui-sans-serif', titleFont: 'ui-sans-serif' },
        legend: { titleFontSize: 11, labelFontSize: 11 },
      },
    };
    specs[name] = spec;

    // Verdict for the row tint: compare the best rhc backend against
    // ghc in the latest run. A program absent from the latest run
    // (renamed/retired bench) is shown neutral. The trend compares
    // the latest gap against the previous run's gap so each row can
    // show whether the program is improving or regressing.
    const p = latest.programs[name];
    const gap = gapIn(latest, name);
    const prevGap = gapIn(previous, name);
    let trend = null;
    if (gap !== null && prevGap !== null) {
      if (gap < prevGap * 0.98) trend = 'up';        // faster than last run
      else if (gap > prevGap * 1.02) trend = 'down'; // slower than last run
      else trend = 'flat';
    }
    rowsMeta.push({
      name,
      gap,
      trend,
      rhc_ms: p ? p.rhc_mean_ms : null,
      rhc_immix_ms: (p && typeof p.rhc_immix_mean_ms === 'number') ? p.rhc_immix_mean_ms : null,
      ghc_ms: p ? p.ghc_mean_ms : null,
    });
  }

  // Headline numbers for the strip above the explorer: how many
  // programs rusholme currently wins, and the geometric mean of the
  // gap across the latest run (the honest single-number summary for
  // ratios — an arithmetic mean would let one outlier dominate).
  const scored = rowsMeta.filter(m => m.gap !== null);
  const wins = scored.filter(m => m.gap <= 1.0).length;
  const losses = scored.length - wins;
  const geomean = scored.length
    ? Math.exp(scored.reduce((acc, m) => acc + Math.log(m.gap), 0) / scored.length)
    : null;
  const geomeanColour = geomean === null ? 'text-gray-400'
    : geomean <= 1.0 ? 'text-emerald-300'
    : geomean <= 1.5 ? 'text-amber-300'
    : 'text-rose-300';

  // One row per benchmark. Tint encodes the latest verdict: emerald
  // when rhc (best backend) matches or beats GHC, soft rose when it
  // trails by up to 50%, stronger rose beyond that. The arrow shows
  // the direction of travel since the previous committed run.
  const trendGlyph = (trend) =>
    trend === 'up' ? '<span class="text-emerald-400" title="faster than previous run">▴</span>'
    : trend === 'down' ? '<span class="text-rose-400" title="slower than previous run">▾</span>'
    : trend === 'flat' ? '<span class="text-gray-600" title="unchanged since previous run">▸</span>'
    : '';

  const rowsHTML = rowsMeta.map(({ name, gap, trend }) => {
    let tint, badge, badgeText;
    if (gap === null) {
      tint = 'border-gray-800 hover:bg-gray-800/60';
      badge = 'text-gray-500';
      badgeText = 'n/a';
    } else if (gap <= 1.0) {
      tint = 'border-emerald-500/30 bg-emerald-500/10 hover:bg-emerald-500/20';
      badge = 'text-emerald-300';
      badgeText = `${(1 / gap).toFixed(2)}× faster`;
    } else if (gap <= 1.5) {
      tint = 'border-rose-500/20 bg-rose-500/5 hover:bg-rose-500/15';
      badge = 'text-rose-300/80';
      badgeText = `${gap.toFixed(2)}× slower`;
    } else {
      tint = 'border-rose-500/40 bg-rose-500/15 hover:bg-rose-500/25';
      badge = 'text-rose-300';
      badgeText = `${gap.toFixed(2)}× slower`;
    }
    return `
        <button type="button" data-bench="${escapeHtml(name)}" data-gap="${gap === null ? '' : gap}"
            class="bench-row w-full flex items-center justify-between gap-3 px-4 py-2.5 rounded-xl border ${tint} transition-all duration-150 text-left">
          <span class="flex items-center gap-2 min-w-0">
            ${trendGlyph(trend)}
            <span class="text-sm font-mono text-gray-200 truncate">${escapeHtml(name)}</span>
          </span>
          <span class="text-xs font-semibold whitespace-nowrap ${badge}">${badgeText}</span>
        </button>`;
  }).join('\n');

  const html = `
    <div class="flex flex-wrap items-center gap-3 mb-6">
      <div class="flex items-center gap-2 rounded-full border border-emerald-500/30 bg-emerald-500/10 px-4 py-1.5">
        <span class="w-2 h-2 rounded-full bg-emerald-400"></span>
        <span class="text-sm text-emerald-300 font-semibold">${wins}</span>
        <span class="text-xs text-gray-400">rusholme wins</span>
      </div>
      <div class="flex items-center gap-2 rounded-full border border-rose-500/30 bg-rose-500/10 px-4 py-1.5">
        <span class="w-2 h-2 rounded-full bg-rose-400"></span>
        <span class="text-sm text-rose-300 font-semibold">${losses}</span>
        <span class="text-xs text-gray-400">ghc wins</span>
      </div>
      ${geomean !== null ? `
      <div class="flex items-center gap-2 rounded-full border border-gray-700 bg-gray-800/60 px-4 py-1.5">
        <span class="text-sm font-semibold ${geomeanColour}">${geomean.toFixed(2)}×</span>
        <span class="text-xs text-gray-400">geometric-mean gap vs GHC</span>
      </div>` : ''}
    </div>
    <div class="flex flex-col lg:flex-row gap-6">
      <div class="lg:w-80 shrink-0 flex flex-col gap-3">
        <div class="flex gap-2">
          <input type="search" id="bench-filter" placeholder="Filter benchmarks…"
              class="flex-1 min-w-0 bg-gray-900/80 border border-gray-700 rounded-xl px-3 py-2 text-sm text-gray-200 placeholder-gray-500 focus:outline-none focus:border-emerald-500/50" />
          <button type="button" id="bench-sort"
              class="shrink-0 bg-gray-900/80 border border-gray-700 rounded-xl px-3 py-2 text-xs text-gray-400 hover:text-gray-200 hover:border-gray-500 transition-colors"
              title="Toggle sort: name / gap">A–Z</button>
        </div>
        <div class="flex flex-col gap-1.5 max-h-[36rem] overflow-y-auto pr-1" id="bench-nav">
${rowsHTML}
        </div>
      </div>
      <div class="flex-1 min-w-0 bg-gray-900/60 rounded-2xl border border-gray-800 p-5 self-start w-full lg:sticky lg:top-24">
        <div class="flex flex-wrap items-baseline justify-between gap-3 mb-1">
          <h3 class="text-base font-mono text-white" id="bench-detail-title"></h3>
          <span class="text-sm font-semibold" id="bench-detail-verdict"></span>
        </div>
        <div class="flex flex-wrap gap-2 mb-4" id="bench-detail-chips"></div>
        <div id="bench-detail-chart" class="w-full" style="min-height: 300px;"></div>
        <p class="text-gray-500 text-xs mt-3">Mean wall-clock per committed run, log scale. Shaded band is ±σ. Hover points for the exact numbers and commit.</p>
      </div>
    </div>
<script>
(function () {
  var SPECS = ${JSON.stringify(specs)};
  var META = ${JSON.stringify(Object.fromEntries(rowsMeta.map(m => [m.name, m])))};
  var selected = null;
  function fmtMs(ms) { return ms >= 100 ? ms.toFixed(0) : ms.toFixed(2); }
  function chip(label, value, colour) {
    return '<span class="inline-flex items-baseline gap-1.5 rounded-lg border border-gray-700/80 bg-gray-800/60 px-2.5 py-1">'
      + '<span class="w-1.5 h-1.5 rounded-full self-center" style="background:' + colour + '"></span>'
      + '<span class="text-xs text-gray-400">' + label + '</span>'
      + '<span class="text-sm font-semibold text-gray-100">' + fmtMs(value) + '</span>'
      + '<span class="text-[10px] text-gray-500">ms</span></span>';
  }
  function select(name) {
    if (!SPECS[name]) return;
    selected = name;
    document.querySelectorAll('#bench-nav .bench-row').forEach(function (row) {
      var active = row.dataset.bench === name;
      row.classList.toggle('ring-2', active);
      row.classList.toggle('ring-emerald-400/40', active);
    });
    document.getElementById('bench-detail-title').textContent = name + '.hs';
    var m = META[name];
    var verdictEl = document.getElementById('bench-detail-verdict');
    var chipsEl = document.getElementById('bench-detail-chips');
    if (m && m.gap !== null) {
      if (m.gap <= 1.0) {
        verdictEl.textContent = (1 / m.gap).toFixed(2) + '× faster than GHC';
        verdictEl.className = 'text-sm font-semibold text-emerald-300';
      } else {
        verdictEl.textContent = m.gap.toFixed(2) + '× slower than GHC';
        verdictEl.className = 'text-sm font-semibold ' + (m.gap <= 1.5 ? 'text-rose-300/80' : 'text-rose-300');
      }
      var chips = [chip('rhc arena', m.rhc_ms, '#34d399')];
      if (m.rhc_immix_ms !== null) chips.push(chip('rhc immix', m.rhc_immix_ms, '#60a5fa'));
      chips.push(chip('ghc', m.ghc_ms, '#f7a41d'));
      chipsEl.innerHTML = chips.join('');
    } else {
      verdictEl.textContent = '';
      chipsEl.innerHTML = '';
    }
    vegaEmbed('#bench-detail-chart', SPECS[name], { actions: false, renderer: 'svg' })
      .catch(function (e) { console.error('vega-embed failed for ' + name + ':', e); });
  }
  function visibleRows() {
    return Array.prototype.filter.call(
      document.querySelectorAll('#bench-nav .bench-row'),
      function (r) { return r.style.display !== 'none'; });
  }
  function init() {
    if (typeof vegaEmbed !== 'function') { console.error('vega-embed not loaded'); return; }
    var nav = document.getElementById('bench-nav');
    if (!nav) return;
    nav.addEventListener('click', function (ev) {
      var row = ev.target.closest('.bench-row');
      if (row) select(row.dataset.bench);
    });
    // Arrow keys walk the (visible) list once a row has focus or a
    // selection exists.
    nav.addEventListener('keydown', function (ev) {
      if (ev.key !== 'ArrowDown' && ev.key !== 'ArrowUp') return;
      ev.preventDefault();
      var rows = visibleRows();
      if (!rows.length) return;
      var idx = rows.findIndex(function (r) { return r.dataset.bench === selected; });
      idx = ev.key === 'ArrowDown' ? Math.min(idx + 1, rows.length - 1) : Math.max(idx - 1, 0);
      select(rows[idx].dataset.bench);
      rows[idx].focus();
      rows[idx].scrollIntoView({ block: 'nearest' });
    });
    var filter = document.getElementById('bench-filter');
    filter.addEventListener('input', function () {
      var q = filter.value.trim().toLowerCase();
      document.querySelectorAll('#bench-nav .bench-row').forEach(function (row) {
        row.style.display = row.dataset.bench.toLowerCase().indexOf(q) === -1 ? 'none' : '';
      });
    });
    // Sort toggle: alphabetical ↔ worst-gap-first. Re-appending the
    // buttons reorders them in place; listeners are delegated so
    // nothing needs rebinding.
    var sortBtn = document.getElementById('bench-sort');
    var byGap = false;
    sortBtn.addEventListener('click', function () {
      byGap = !byGap;
      sortBtn.textContent = byGap ? 'gap' : 'A–Z';
      var rows = Array.prototype.slice.call(document.querySelectorAll('#bench-nav .bench-row'));
      rows.sort(function (a, b) {
        if (!byGap) return a.dataset.bench.localeCompare(b.dataset.bench);
        var ga = a.dataset.gap === '' ? -Infinity : parseFloat(a.dataset.gap);
        var gb = b.dataset.gap === '' ? -Infinity : parseFloat(b.dataset.gap);
        return gb - ga;
      });
      rows.forEach(function (r) { nav.appendChild(r); });
    });
    var first = nav.querySelector('.bench-row');
    if (first) select(first.dataset.bench);
  }
  if (document.readyState === 'loading') {
    document.addEventListener('DOMContentLoaded', init);
  } else {
    init();
  }
})();
</script>`;

  return html;
}

// Main build function
async function build() {
  console.log('🏗️  Building Rusholme website...\n');
  
  // Copy logo from assets
  copyLogo();

  // Copy WASM REPL binary from zig build output
  copyReplWasm();
  
  const templatePath = path.join(__dirname, 'template.html');
  if (!fs.existsSync(templatePath)) {
    console.error('❌ Error: template.html not found!');
    process.exit(1);
  }
  
  let html = fs.readFileSync(templatePath, 'utf-8');
  
  // Compute milestone progress from ROADMAP.md
  console.log('📊 Computing milestone progress...');
  const milestones = computeMilestoneProgress();
  for (const m of milestones) {
    console.log(`   ${m.id}: ${m.done}/${m.total} done (${m.percentage}%)`);
  }

  const milestonePlaceholder = '<!-- MILESTONE_CARDS_PLACEHOLDER -->';
  if (html.includes(milestonePlaceholder)) {
    html = html.replace(milestonePlaceholder, generateMilestoneCardsHTML(milestones));
    console.log('   ✓ Replaced milestone cards with computed progress');
  } else {
    console.log('   ⚠️  No milestone placeholder found in template.html');
  }

  // Fetch GitHub issues
  console.log('📥 Fetching GitHub issues...');
  const issues = await fetchRecentIssues();
  
  if (issues.length > 0) {
    console.log(`   ✓ Found ${issues.length} recent issues`);
  }
  
  // Generate the HTML replacement
  const recentProgressHTML = generateRecentProgressHTML(issues);
  
  // Replace the placeholder comment with actual HTML
  const placeholder = `<!-- RECENT_ISSUES_PLACEHOLDER -->`;
  const replacement = recentProgressHTML;
  
  if (html.includes(placeholder)) {
    html = html.replace(placeholder, replacement);
    console.log('   ✓ Replaced placeholder with GitHub data');
  } else {
    console.log('   ⚠️  No placeholder found in template.html');
  }
  
  // Benchmark section is now rendered dynamically at runtime
  // from bench/results.json (fetched client-side).
  // The template already contains the full interactive explorer
  // that fetches the JSON file — no build-time replacement needed.

  // Stage bench/results.json next to index.html so the client-side
  // fetch('bench/results.json') resolves both locally (`npm run serve`
  // serves website/ as the site root) and on CI (which mirrors this
  // layout by copying the file into _site/bench/). website/bench/ is
  // generated output and gitignored.
  const benchSrc = path.join(__dirname, '../bench/results.json');
  if (fs.existsSync(benchSrc)) {
    const benchOutDir = path.join(__dirname, 'bench');
    fs.mkdirSync(benchOutDir, { recursive: true });
    fs.copyFileSync(benchSrc, path.join(benchOutDir, 'results.json'));
    console.log('   ✓ Staged bench/results.json for local serving');
  } else {
    console.log('   ⚠️  ../bench/results.json missing — bench explorer will 404');
  }

  // Write output
  const outputPath = path.join(__dirname, 'index.html');
  fs.writeFileSync(outputPath, html, 'utf-8');
  
  console.log(`\n✅ Built successfully!`);
  console.log(`   Output: ${outputPath}`);
  console.log(`   Size: ${(html.length / 1024).toFixed(1)} KB\n`);
}

build().catch(err => {
  console.error('\n❌ Build failed:', err.message);
  console.error(err.stack);
  process.exit(1);
});
