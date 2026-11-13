#!/usr/bin/env bash
# Usage: ZLIB_SRC=<zlib checkout> bash tests/regression/inflate-shared-block/run.sh
# Builds the patched zlib copy under ASan and UBSan and inflates with the input and
# the output in one heap block (disjoint ranges). It must decode correctly with no
# sanitizer report: this layout is defined C, so the proofs must cover it.
set -uo pipefail
here=$(cd "$(dirname "$0")" && pwd)
src=${ZLIB_SRC:?set ZLIB_SRC to the pinned zlib checkout}
work=${WORK:-$here/../../build/inflate-shared-block}
mkdir -p "$work"
CFLAGS="-fsanitize=address,undefined -fno-sanitize-recover=all -g -O1" \
  bash "$here/../../build-zlib.sh" "$src" "$work/z" >/dev/null || exit 2
cc -g -fsanitize=address,undefined -fno-sanitize-recover=all -I"$work/z" \
  "$here/shared.c" "$work/z/libz.a" -o "$work/shared" || exit 2
out=$("$work/shared" 2>&1); status=$?
printf '%s\n' "$out"
if [ $status -eq 0 ] && ! printf '%s\n' "$out" | grep -q "runtime error\|AddressSanitizer"; then
  echo "ok: shared block, no sanitizer report"; exit 0
fi
echo "FAIL: shared block"; exit 1
