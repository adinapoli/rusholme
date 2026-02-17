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

// Main build function
async function build() {
  console.log('🏗️  Building Rusholme website...\n');
  
  // Copy logo from assets
  copyLogo();
  
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
