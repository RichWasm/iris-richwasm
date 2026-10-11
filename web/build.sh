#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
root=$(pwd)
dist=$root/web/dist
dune build ./web/page.bc.js ./web/compiler_worker.bc.js ./src/runtime/richwasm.wasm --profile release
(cd web/js && npm install --no-audit --no-fund --silent)
rm -rf "$dist" && mkdir -p "$dist"
cp web/static/* "$dist"
cp _build/default/web/page.bc.js _build/default/web/compiler_worker.bc.js _build/default/src/runtime/richwasm.wasm "$dist"
cd web/js
for grammar in grammars/*.grammar; do npx lezer-generator "$grammar" -o "$grammar.js"; done
esbuild editor_entry.js --bundle --format=iife --minify --outfile="$dist/editor_entry.js"
esbuild compiler_worker_entry.js --bundle --format=iife --minify --platform=browser --external:fs --external:path --outfile="$dist/compiler_worker.js"
esbuild run_worker.ts --bundle --format=iife --minify --outfile="$dist/run_worker.js"
