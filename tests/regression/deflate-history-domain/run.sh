#!/usr/bin/env bash
# Usage: ZLIB_SRC=<zlib checkout> bash tests/regression/deflate-history-domain/run.sh
# Builds the patched zlib copy under ASan and UBSan and runs the three histories. Each must be
# reported by a sanitizer: they are outside the documented use and outside the corrected
# history domain (DeflateNotStarted, DeflateHeaderProgress in ZlibF/Spec/Public/History.lean).
set -uo pipefail
here=$(cd "$(dirname "$0")" && pwd)
src=${ZLIB_SRC:?set ZLIB_SRC to the pinned zlib checkout}
work=${WORK:-$here/../../build/deflate-history-domain}
mkdir -p "$work"
CFLAGS="-fsanitize=address,undefined -g -O1" bash "$here/../../build-zlib.sh" "$src" "$work/z" >/dev/null || exit 2
flags="-g -fsanitize=address,undefined -I$work/z"
cc $flags "$here/prime.c" "$work/z/libz.a" -o "$work/prime" || exit 2
cc $flags "$here/header.c" "$work/z/libz.a" -o "$work/header" || exit 2
fail=0
expect() {
  local name=$1 pattern=$2; shift 2
  local out
  out=$("$@" 2>&1)
  if printf '%s\n' "$out" | grep -q "$pattern"; then echo "ok: $name"; else echo "MISSING: $name"; fail=1; fi
}
expect "deflatePrime after symbols: read outside _dist_code" "index 767 out of bounds" "$work/prime"
expect "deflateSetHeader(NULL) inside the header: NULL dereference" "null pointer\|SEGV" "$work/header" 1
expect "extra_len shrunk inside the header: read past the buffer" "heap-buffer-overflow" "$work/header" 2
exit $fail
