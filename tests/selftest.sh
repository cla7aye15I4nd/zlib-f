#!/usr/bin/env bash
# Mutation check of the harness itself: change one thing in a COPY of the Lean translation and check
# that run.sh reports a difference. A mutation marked `detect` must be caught; one marked `same` is an
# equivalent mutant (the result cannot change) and must NOT be reported. Exit 0 iff all as expected.
#
#   ZLIB_SRC=<zlib checkout> bash tests/selftest.sh     (or ZLIB_BUILD=<dir> as for run.sh)
#   ONLY=<name>  run only the mutation file mutations/<name>.tsv
#
# The proofs in a translation module would not check after a mutation, so the copy keeps only the
# translation: the module text up to the first line `end Zlib.<Name>`. The first step runs the harness
# on this unmutated truncated copy and requires it to pass, so the truncation is shown to be faithful.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
export PATH="$HOME/zlib-claude/bin:$HOME/.elan/bin:$PATH"  # lake: the gated wrapper first
ws=$(cd "$here/.." && pwd)
ZLIB_BUILD=${ZLIB_BUILD:-$here/build/zlib}
if [ ! -f "$ZLIB_BUILD/libz.a" ]; then
  [ -n "${ZLIB_SRC:-}" ] || { echo "selftest.sh: set ZLIB_SRC or ZLIB_BUILD" >&2; exit 2; }
  bash "$here/build-zlib.sh" "$ZLIB_SRC" "$ZLIB_BUILD"
fi
ZLIB_BUILD=$(cd "$ZLIB_BUILD" && pwd)
tmp=$(mktemp -d "${TMPDIR:-/tmp}/difftest-selftest.XXXXXX")
trap 'rm -rf "$tmp"' EXIT
copy="$tmp/ws"
mkdir -p "$copy"
(cd "$ws" && tar --exclude=.git --exclude=tests/build --exclude=zlib -cf - .) | tar -C "$copy" -xf -
export ZLIB_BUILD
fail=0; nd=0; ns=0
for tsv in "$here"/mutations/*.tsv; do
  name=$(basename "$tsv" .tsv)
  [ -z "${ONLY:-}" ] || [ "$ONLY" = "$name" ] || continue
  # every file the mutation list touches (usually one; gz.tsv has several)
  files=$(grep -v '^#' "$tsv" | cut -f3 | sort -u)
  for file in $files; do
    awk '{print} /^end Zlib\.[A-Za-z0-9_]+[[:space:]]*$/ {exit}' "$ws/$file" > "$tmp/$(echo "$file" | tr / _).orig"
  done
  restore() { for file in $files; do cp "$tmp/$(echo "$file" | tr / _).orig" "$copy/$file"; done; }
  restore
  echo "--- $name: unmutated, truncated to the translation (must pass)"
  if ! ONLY=$name bash "$copy/tests/run.sh" > "$tmp/base.log" 2>&1; then
    tail -20 "$tmp/base.log"; echo "SELFTEST FAILED: the unmutated truncated copy does not pass"; exit 1
  fi
  tail -1 "$tmp/base.log"
  while IFS=$'\t' read -r mname expect mfile occ old new; do
    case "$mname" in ''|'#'*) continue;; esac
    restore
    python3 "$here/mutate.py" "$copy/$mfile" "$occ" "$old" "$new"
    if ONLY=$name bash "$copy/tests/run.sh" > "$tmp/m.log" 2>&1; then verdict=same
    elif grep -q '^DIFFERENCE' "$tmp/m.log"; then verdict=detect
    else tail -20 "$tmp/m.log"; echo "SELFTEST FAILED: mutation $mname did not build or run"; exit 1; fi
    if [ "$verdict" = "$expect" ]; then ok=ok; else ok=UNEXPECTED; fail=1; fi
    first=$(grep '^DIFFERENCE' -A1 "$tmp/m.log" | cut -c1-110 | tr '\n' ' ' || true)
    printf '%-34s expected %-6s got %-6s %s %s\n' "$mname" "$expect" "$verdict" "$ok" "$first"
    if [ "$expect" = detect ]; then nd=$((nd+1)); else ns=$((ns+1)); fi
  done < "$tsv"
done
echo "$nd mutations that must be detected, $ns equivalent mutants that must not be"
if [ "$fail" = 0 ]; then echo "SELFTEST PASS"; else echo "SELFTEST FAIL: see UNEXPECTED above"; exit 1; fi
