#!/usr/bin/env bash
# Self test of the audit: every file in tests/audit/cheats must be rejected.
#   *.lean  a new module with a forbidden construct; it is added to the build
#   *.mut   one replacement  FILE|||OLD|||NEW  in the sources (a weaker runtime, a changed statement, ...)
# A cheat counts as rejected if the build fails, or the audit fails, or a lock differs.
set -u
cd "$(dirname "$0")/../.."
status=0
for c in tests/audit/cheats/*.lean tests/audit/cheats/*.mut; do
  name=$(basename "$c")
  tmp=$(mktemp -d)
  rsync -a --exclude .lake --exclude .git ./ "$tmp/"
  if [[ "$c" == *.lean ]]; then
    cp "$c" "$tmp/ZlibF/Cheat.lean"
    echo "import ZlibF.Cheat" >> "$tmp/ZlibF.lean"
  else
    python3 - "$tmp" "$c" <<'PY'
import sys
tmp, spec = sys.argv[1], sys.argv[2]
f, old, new = open(spec).read().rstrip('\n').split('|||')
p = f'{tmp}/{f}'
s = open(p).read()
assert old in s, 'mutation does not apply: ' + old[:40]
open(p, 'w').write(s.replace(old, new, 1))
PY
    [ $? -eq 0 ] || { echo "ERROR  $name: the mutation does not apply"; status=1; continue; }
  fi
  rejected=no
  if ! (cd "$tmp" && lake build ZlibF >/dev/null 2>&1); then
    rejected="build fails"
  else
    (cd "$tmp" && lake env lean --run tests/audit/Audit.lean tests/audit/theorems.txt > report.txt 2> err.txt)
    if [ $? -ne 0 ]; then rejected="audit fails"
    elif ! diff -q <(grep '^trusted ' "$tmp/report.txt") tests/audit/trusted.lock >/dev/null; then rejected="trusted lock differs"
    elif ! diff -q <(grep '^statement ' "$tmp/report.txt") tests/audit/statements.lock >/dev/null; then rejected="statement lock differs"
    fi
  fi
  if [ "$rejected" = no ]; then echo "NOT DETECTED  $name"; status=1; else echo "rejected  $name ($rejected)"; fi
  rm -rf "$tmp"
done
exit $status
