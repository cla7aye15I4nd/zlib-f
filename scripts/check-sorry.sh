#!/usr/bin/env bash
# Sorry ratchet: the number of `sorry` in the Lean sources may not exceed sorry-budget.txt.
# A series of changes lowers the budget; the last one sets it to 0.
set -euo pipefail
cd "$(dirname "$0")/.."
budget=$(tr -d '[:space:]' < sorry-budget.txt)
count=$( (grep -rwn --include='*.lean' 'sorry' ZlibF ZlibF.lean 2>/dev/null || true) \
         | grep -v -- '--.*sorry' | grep -vc '^\S*:[0-9]*:\s*/\?-' || true)
echo "sorry count: $count (budget: $budget)"
if [ "$count" -gt "$budget" ]; then
  echo "error: more sorry than the budget allows" >&2
  exit 1
fi
