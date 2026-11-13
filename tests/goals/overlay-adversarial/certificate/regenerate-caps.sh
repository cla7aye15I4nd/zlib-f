#!/usr/bin/env bash
# Usage: [PYTHON=python3] bash tests/goals/overlay-adversarial/certificate/regenerate-caps.sh
# Regenerates the repair-cap case analyses (ZlibF/Math/RepairCap13*, RepairCap15*) with
# repair_caps.py and compares them with the repository copies.
# Exit 0: identical. Exit 1: a file differs (the diff is printed).
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../../../.." && pwd)
py=${PYTHON:-python3}
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
"$py" "$here/repair_caps.py" 13 29 2 "$tmp"
"$py" "$here/repair_caps.py" 15 245 0 "$tmp"
status=0
for tag in RepairCap13 RepairCap15; do
  if diff -ru "$repo/ZlibF/Math/$tag" "$tmp/$tag" && diff -u "$repo/ZlibF/Math/$tag.lean" "$tmp/$tag.lean"; then
    echo "repair caps: $tag regenerated identically"
  else
    echo "repair caps: $tag differs" >&2
    status=1
  fi
done
exit $status
