#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"

ref=${1:-HEAD}
out=iris-richwasm-artifact.tar.gz
root=iris-richwasm-artifact
exclude=(.github notes package.sh)

staging=$(mktemp -d)
trap 'rm -rf "$staging"' EXIT

git archive --format=tar --prefix="$root/" "$ref" | tar -x -C "$staging"
for p in "${exclude[@]}"; do rm -rf "${staging:?}/$root/$p"; done

deny='brianna|ryan|owen|elan|mathias|lars|amal|ari|maxime'
hits=$({  rg -inw -. --no-ignore "$deny" "$staging/$root" || true; })
if [ -n "$hits" ]; then
  printf '%s\n' "$hits" >&2
  echo 'FAILED: Deanonymizing information would be included' >&2
  exit 1
fi

# override owner and group to prevent username leaking
tar -C "$staging" --sort=name --owner=0 --group=0 --numeric-owner \
    --mtime='2026-07-09 00:00:00Z' -cf - "$root" | gzip -n >"$out"
sha256sum "$out"
