#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
echo "Building Rusholme (zig build)..."
zig build
echo "Building website..."
cd website
node build.js
echo "Serving website on http://localhost:3000"
npx serve .
