#!/usr/bin/env bash
# Usage: [PYTHON=python3] bash tests/goals/overlay-adversarial/certificate/regenerate.sh
# Regenerates both overlay certificates and compares them with the Lean files in the repository:
# memLevel 2 (overlay_cert.py, the solver built from lpsolve.c) and memLevel 1 (overlay_cert128.py,
# exact LP with the z3 Python module; set PYTHON to an interpreter that has it).
# Exit 0: both identical. Exit 1: a file differs (the diff is printed).
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../../../.." && pwd)
py=${PYTHON:-python3}
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
cc -O2 -o "$tmp/lpsolve" "$here/lpsolve.c"
LPSOLVE="$tmp/lpsolve" "$py" "$here/overlay_cert.py" --lean "$tmp/DeflateOverlayCertificate.lean"
"$py" -c 'import z3' 2>/dev/null || { echo "certificate: $py has no z3 module (set PYTHON)" >&2; exit 2; }
"$py" "$here/overlay_cert128.py" --lean "$tmp/DeflateOverlayCertificate128.lean"
status=0
for f in DeflateOverlayCertificate.lean DeflateOverlayCertificate128.lean; do
  if diff -u "$repo/ZlibF/Math/$f" "$tmp/$f"; then
    echo "certificate: $f regenerated identically"
  else
    echo "certificate: $f differs" >&2
    status=1
  fi
done
exit $status
