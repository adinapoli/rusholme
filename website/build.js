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
