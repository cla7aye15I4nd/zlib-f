#!/usr/bin/env bash
# No `sorry` is allowed in the Lean sources.
set -euo pipefail
cd "$(dirname "$0")/.."
count=$( (grep -rwn --include='*.lean' 'sorry' ZlibF ZlibF.lean 2>/dev/null || true) \
         | grep -v -- '--.*sorry' | grep -vc '^\S*:[0-9]*:\s*/\?-' || true)
echo "sorry count: $count"
if [ "$count" -gt 0 ]; then
  echo "error: sorry is not allowed" >&2
  exit 1
fi
