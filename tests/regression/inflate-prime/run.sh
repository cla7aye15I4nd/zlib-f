#!/usr/bin/env bash
# Boundary regression for inflatePrime: the real C against the Lean translation,
# on the same fresh-stream and append-sequence cases, compared byte for byte.
#
#   bash tests/regression/inflate-prime/run.sh          # normal build
#   SAN=1 bash tests/regression/inflate-prime/run.sh    # ASan/UBSan/LSan build
#   ZLIB_BUILD=<dir> ...                                # an existing patched build
#
# Evidence, not proof. Exit 0 identical, 1 a difference or fault, 2 a setup error.
set -euo pipefail

root=$(cd "$(dirname "$0")/../../.." && pwd)
cd "$root"

work="$root/tests/build/inflate-prime"
mkdir -p "$work"

zlib="${ZLIB_BUILD:-}"
if [ -z "$zlib" ]; then
  if [ "${SAN:-0}" = 1 ]; then zlib="$root/tests/build/zlib-san"; else zlib="$root/tests/build/zlib"; fi
fi
[ -f "$zlib/libz.a" ] || { echo "run.sh: no libz.a under $zlib" >&2; exit 2; }
zlib=$(cd "$zlib" && pwd)

cflags="-O2 -g -Wall -Wextra"
if [ "${SAN:-0}" = 1 ]; then
  cflags="-O1 -g -fsanitize=address,undefined -fno-sanitize-recover=undefined"
fi

echo "== building the C harness ($zlib)"
# shellcheck disable=SC2086
cc $cflags -I"$zlib" tests/regression/inflate-prime/prime.c "$zlib/libz.a" \
  -o "$work/prime_c" 2> "$work/prime_c.build.log"

echo "== building and running the Lean harness"
if ! lake build 'ZlibF.Zlib.«inflate.c»' 'ZlibF.Zlib.«zutil.c»' \
    > "$work/lean-build.log" 2>&1; then
  cat "$work/lean-build.log" >&2; exit 2
fi
if ! lake env lean --run tests/regression/inflate-prime/prime.lean \
    > "$work/prime_lean.out" 2> "$work/prime_lean.err"; then
  echo "run.sh: the Lean harness failed" >&2
  cat "$work/prime_lean.out" "$work/prime_lean.err" >&2; exit 1
fi

echo "== running both"
if [ "${SAN:-0}" = 1 ]; then
  env -u LSAN_OPTIONS ASAN_OPTIONS=detect_leaks=1:halt_on_error=1 \
    UBSAN_OPTIONS=halt_on_error=1 "$work/prime_c" > "$work/prime_c.out" \
    2> "$work/prime_c.err"
else
  "$work/prime_c" > "$work/prime_c.out" 2> "$work/prime_c.err"
fi
if [ -s "$work/prime_c.err" ]; then echo "run.sh: C harness wrote to stderr:" >&2; cat "$work/prime_c.err" >&2; exit 1; fi
if [ -s "$work/prime_lean.err" ]; then
  echo "run.sh: Lean harness wrote to stderr:" >&2; cat "$work/prime_lean.err" >&2; exit 1
fi

if [ "$(wc -l < "$work/prime_c.out")" -ne 366 ] ||
   [ "$(wc -l < "$work/prime_lean.out")" -ne 366 ]; then
  echo "DIFFERENCE: expected 366 observed-state lines" >&2; exit 1
fi
if ! grep -Fxq 'prime b=1 v=-1 rc=0 hold=1 bits=1' "$work/prime_c.out"; then
  echo "DIFFERENCE: missing negative-value baseline" >&2; exit 1
fi
if ! cmp "$work/prime_c.out" "$work/prime_lean.out"; then
  echo "DIFFERENCE: outputs differ"
  echo "  C    : $work/prime_c.out"
  echo "  Lean : $work/prime_lean.out"
  diff "$work/prime_c.out" "$work/prime_lean.out" | head -20
  exit 1
fi
echo "PASS: $(grep -c . "$work/prime_c.out") output lines identical (fault-free)"
