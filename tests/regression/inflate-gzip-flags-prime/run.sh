#!/usr/bin/env bash
# Usage: ZLIB_SRC=<zlib checkout> bash tests/regression/inflate-gzip-flags-prime/run.sh
# Builds the patched zlib copy under ASan and UBSan. After the gzip magic, two
# inflatePrime calls give FLAGS 32 held bits; FLAGS stores (int)hold, a word that
# does not fit in 16 bits. No sanitizer report: the state is reachable and defined.
set -uo pipefail
here=$(cd "$(dirname "$0")" && pwd)
src=${ZLIB_SRC:?set ZLIB_SRC to the pinned zlib checkout}
work=${WORK:-$here/../../build/inflate-gzip-flags-prime}
mkdir -p "$work"
CFLAGS="-fsanitize=address,undefined -g -O1" bash "$here/../../build-zlib.sh" "$src" "$work/z" >/dev/null || exit 2
cc -g -fsanitize=address,undefined -I"$work/z" -I"$src" "$here/prime.c" "$work/z/libz.a" -o "$work/prime" || exit 2
out=$("$work/prime" 2>&1) || { printf '%s\n' "$out"; exit 1; }
printf '%s\n' "$out"
fail=0
printf '%s\n' "$out" | grep -q "flags 65544 " || { echo "MISSING: flags 65544"; fail=1; }
printf '%s\n' "$out" | grep -q "flags -2147483640 " || { echo "MISSING: flags -2147483640"; fail=1; }
printf '%s\n' "$out" | grep -qi "sanitizer" && { echo "UNEXPECTED sanitizer report"; fail=1; }
exit $fail
