#!/usr/bin/env bash
# Usage: bash tests/goals/overlay-adversarial/certificate/regenerate.sh
# Regenerates the memLevel 2 certificate (overlay_cert.py --lean) and compares it with the Lean file
# in the repository. Exit 0: identical. Exit 1: they differ (the diff is printed).
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../../../.." && pwd)
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
cc -O2 -o "$tmp/lpsolve" "$here/lpsolve.c"
LPSOLVE="$tmp/lpsolve" python3 "$here/overlay_cert.py" --lean "$tmp/DeflateOverlayCertificate.lean"
if diff -u "$repo/ZlibF/Math/DeflateOverlayCertificate.lean" "$tmp/DeflateOverlayCertificate.lean"; then
  echo "certificate: regenerated file is identical"
else
  echo "certificate: regenerated file differs" >&2
  exit 1
fi
