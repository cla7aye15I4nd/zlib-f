#!/usr/bin/env bash
# Usage: ZLIB_SRC=<zlib checkout> bash tests/regression/inflate-gzip-extra/run.sh
# Builds the patched zlib copy under ASan and UBSan and runs the two gzip extra-field cases.
# Each must be reported by a sanitizer: both are outside the domain of the gzip header
# dispatch theorem (ExtraApart and the EXTRA length premise of
# inflate_dispatch_gzip_header_rank, ZlibF/Proof/inflate.c.gzip-header-dispatch.lean).
set -uo pipefail
here=$(cd "$(dirname "$0")" && pwd)
src=${ZLIB_SRC:?set ZLIB_SRC to the pinned zlib checkout}
work=${WORK:-$here/../../build/inflate-gzip-extra}
mkdir -p "$work"
CFLAGS="-fsanitize=address,undefined -g -O1" bash "$here/../../build-zlib.sh" "$src" "$work/z" >/dev/null || exit 2
flags="-g -fsanitize=address,undefined -I$work/z"
cc $flags "$here/overlap.c" "$work/z/libz.a" -o "$work/overlap" || exit 2
cc $flags "$here/shrink.c" "$work/z/libz.a" -o "$work/shrink" || exit 2
fail=0
expect() {
  local name=$1 pattern=$2; shift 2
  local out
  out=$(ASAN_OPTIONS=allocator_may_return_null=1 "$@" 2>&1)
  if printf '%s\n' "$out" | grep -q "$pattern"; then echo "ok: $name"; else echo "MISSING: $name"; fail=1; fi
}
expect "extra buffer overlapping the unread input: memcpy overlap" "memcpy-param-overlap" "$work/overlap"
expect "extra_len lowered inside the extra field: write past extra_max" "heap-buffer-overflow" "$work/shrink"
exit $fail
