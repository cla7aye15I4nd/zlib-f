#!/usr/bin/env bash
# Usage: ZLIB_SRC=<zlib checkout> bash tests/regression/inflate-gzip-flags-prime/run.sh
# Builds the patched zlib copy under ASan and UBSan and checks that inflatePrime in FLAGS
# makes the C write a gzip flags word of at least 65536, with no sanitizer report.
set -uo pipefail
here=$(cd "$(dirname "$0")" && pwd)
src=${ZLIB_SRC:?set ZLIB_SRC to the pinned zlib checkout}
work=${WORK:-$here/../../build/inflate-gzip-flags-prime}
mkdir -p "$work"
CFLAGS="-fsanitize=address,undefined -g -O1" bash "$here/../../build-zlib.sh" "$src" "$work/z" >/dev/null || exit 2
cc -g -fsanitize=address,undefined -fno-sanitize-recover=all -I"$work/z" "$here/prime.c" "$work/z/libz.a" \
  -o "$work/prime" || exit 2
out=$("$work/prime" 2>&1) || { printf '%s\n' "$out"; echo "MISSING: run failed"; exit 1; }
printf '%s\n' "$out"
if printf '%s\n' "$out" | grep -q '^flags: ret=0 mode=16183 flags=65544$'; then
  echo "ok: flags word 65544 after inflatePrime in FLAGS"
else
  echo "MISSING: flags word 65544"; exit 1
fi
