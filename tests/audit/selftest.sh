#!/usr/bin/env bash
# Every cheat must be rejected, starting from one immutable passing snapshot.
set -euo pipefail
cd "$(dirname "$0")/../.."
base=$(mktemp -d)
report=$(mktemp)
selection=$(mktemp)
tmp=""
cleanup() {
  rm -rf "$base"
  rm -f "$report" "$selection"
  if [ -n "$tmp" ]; then rm -rf "$tmp"; fi
}
trap cleanup EXIT
rsync -a --exclude .lake --exclude .git --exclude zlib --exclude tests/build ./ "$base/"
rsync -a .lake/ "$base/.lake/"
python3 "$base/scripts/select-audit-cheats.py" "$base/tests/audit/cheats" \
  "${AUDIT_SHARD_COUNT-1}" "${AUDIT_SHARD_INDEX-0}" > "$selection"
# Neither a broken baseline nor a concurrent source edit may make a cheat appear detected.
(cd "$base" && lake build ZlibF >/dev/null 2>&1)
(cd "$base" && lake env lean --run tests/audit/Audit.lean tests/audit/theorems.txt > "$report")
(cd "$base" && python3 scripts/check-audit-report.py "$report")
echo "baseline passed"
status=0
while IFS= read -r c; do
  name=$(basename "$c")
  tmp=$(mktemp -d)
  rsync -a "$base/" "$tmp/"
  if [[ "$c" == *.lean ]]; then
    cp "$c" "$tmp/ZlibF/Cheat.lean"
    echo "import ZlibF.Cheat" >> "$tmp/ZlibF.lean"
  else
    if ! python3 - "$tmp" "$c" <<'PY'
import sys
from pathlib import Path
root, spec = sys.argv[1:]
f, old, new = Path(spec).read_text().rstrip('\n').split('|||')
p = Path(root) / f
s = p.read_text()
if s.count(old) != 1:
    sys.exit('mutation must match exactly once: ' + old[:40])
p.write_text(s.replace(old, new, 1))
PY
    then
      echo "ERROR $name: the mutation does not apply"
      status=1
      rm -rf "$tmp"
      tmp=""
      continue
    fi
  fi
  rejected=no
  if ! (cd "$tmp" && lake build ZlibF >/dev/null 2>&1); then
    rejected="build fails"
  elif ! (cd "$tmp" && lake env lean --run "$base/tests/audit/Audit.lean" tests/audit/theorems.txt > report.txt 2> err.txt); then
    rejected="audit fails"
  elif ! (cd "$base" && python3 scripts/check-audit-report.py "$tmp/report.txt" >/dev/null 2>&1); then
    rejected="semantic lock differs"
  fi
  if [ "$rejected" = no ]; then
    echo "NOT DETECTED $name"
    status=1
  else
    echo "rejected $name ($rejected)"
  fi
  rm -rf "$tmp"
  tmp=""
done < "$selection"
exit "$status"
