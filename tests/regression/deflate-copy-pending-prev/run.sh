#!/usr/bin/env bash
# Usage: ZLIB_SRC=<zlib checkout> bash tests/regression/deflate-copy-pending-prev/run.sh
# Builds zlib under ASan and UBSan and runs copy.c: deflateResetKeep, deflate(Z_BLOCK), deflateCopy,
# then on the copy a Z_RLE flush and a default-strategy deflate. AddressSanitizer must report the
# read in longest_match of an uninitialised prev slot's candidate. When valgrind is installed, a
# second build without sanitizers runs `copy plain` (default allocator) under memcheck, which must
# report the use of the uninitialised slot in longest_match. The history is outside the proved
# domain: a direct deflateResetKeep is not a deflate stream operation (docs/deviations.md).
set -uo pipefail
here=$(cd "$(dirname "$0")" && pwd)
src=${ZLIB_SRC:?set ZLIB_SRC to the pinned zlib checkout}
work=${WORK:-$here/../../build/deflate-copy-pending-prev}
mkdir -p "$work"
CFLAGS="-fsanitize=address,undefined -g -O1" bash "$here/../../build-zlib.sh" "$src" "$work/z" >/dev/null || exit 2
cc -g -fsanitize=address,undefined -I"$work/z" -I"$src" "$here/copy.c" "$work/z/libz.a" -o "$work/copy" || exit 2
fail=0
out=$("$work/copy" 2>&1)
printf '%s\n' "$out"
if printf '%s\n' "$out" | grep -q "heap-buffer-overflow" && printf '%s\n' "$out" | grep -q "in longest_match"; then
  echo "ok: deflateCopy after deflateResetKeep, then Z_RLE: longest_match reads past the window"
else
  echo "MISSING: no heap-buffer-overflow in longest_match"; fail=1
fi
if command -v valgrind >/dev/null; then
  CFLAGS="-g -O1" bash "$here/../../build-zlib.sh" "$src" "$work/plain" >/dev/null || exit 2
  cc -g -O1 -I"$work/plain" -I"$src" "$here/copy.c" "$work/plain/libz.a" -o "$work/copy-plain" || exit 2
  out=$(valgrind --track-origins=yes "$work/copy-plain" plain 2>&1)
  printf '%s\n' "$out"
  if printf '%s\n' "$out" | grep -q "uninitialised value" && printf '%s\n' "$out" | grep -q "longest_match"; then
    echo "ok: the default allocator: longest_match uses the uninitialised prev slot"
  else
    echo "MISSING: no uninitialised use in longest_match under valgrind"; fail=1
  fi
fi
exit $fail
