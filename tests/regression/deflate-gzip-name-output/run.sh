#!/usr/bin/env bash
# Usage: ZLIB_SRC=<zlib checkout> bash tests/regression/deflate-gzip-name-output/run.sh
# Builds the patched zlib copy under ASan and UBSan and runs the two gzip name layouts.
# Each must be reported by a sanitizer: both are outside the domain of Goal.deflate
# (DeflateHeaderApart, a conjunct of ActiveHeader, ZlibF/Spec/Public/History.lean).
set -uo pipefail
here=$(cd "$(dirname "$0")" && pwd)
src=${ZLIB_SRC:?set ZLIB_SRC to the pinned zlib checkout}
work=${WORK:-$here/../../build/deflate-gzip-name-output}
mkdir -p "$work"
CFLAGS="-fsanitize=address,undefined -g -O1" bash "$here/../../build-zlib.sh" "$src" "$work/z" >/dev/null || exit 2
flags="-g -fsanitize=address,undefined -I$work/z"
cc $flags "$here/output.c" "$work/z/libz.a" -o "$work/output" || exit 2
cc $flags "$here/pending.c" "$work/z/libz.a" -o "$work/pending" || exit 2
fail=0
expect() {
  local name=$1 pattern=$2; shift 2
  local out
  out=$(ASAN_OPTIONS=detect_leaks=0 "$@" 2>&1)
  if printf '%s\n' "$out" | grep -q "$pattern"; then echo "ok: $name"; else echo "MISSING: $name"; fail=1; fi
}
expect "name in the output range: read past the name buffer" "heap-buffer-overflow" "$work/output"
expect "name in pending_buf: read past pending_buf" "heap-buffer-overflow" "$work/pending"
exit $fail
