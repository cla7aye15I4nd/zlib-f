#!/usr/bin/env bash
# Reproduce the recorded raw fixed-block call sequence. Evidence, not proof.
set -euo pipefail
root=$(cd "$(dirname "$0")/../../.." && pwd)
cd "$root"
variant=normal
cflags=(-O2 -g -Wall -Wextra)
if [ "${SAN:-0}" = 1 ]; then
  variant=san
  cflags=(-O1 -g -Wall -Wextra -fsanitize=address,undefined -fno-sanitize-recover=undefined)
fi
work="$root/tests/build/inflate-deferred-distance/$variant"
mkdir -p "$work"
zlib="${ZLIB_BUILD:-$root/tests/build/zlib}"
if [ "${SAN:-0}" = 1 ] && [ -z "${ZLIB_BUILD:-}" ]; then
  zlib="$root/tests/build/zlib-san"
fi
[ -f "$zlib/libz.a" ] || { echo "missing patched libz.a: $zlib" >&2; exit 2; }
zlib=$(cd "$zlib" && pwd)
if ! cc "${cflags[@]}" -I"$zlib" tests/regression/inflate-deferred-distance/distance.c \
    "$zlib/libz.a" -o "$work/distance-c" > "$work/c-build.log" 2>&1; then
  cat "$work/c-build.log" >&2; exit 2
fi
if ! lake build 'ZlibF.Zlib.«inflate.c»' 'ZlibF.Zlib.«zutil.c»' \
    > "$work/lean-build.log" 2>&1; then
  cat "$work/lean-build.log" >&2; exit 2
fi
if ! lake env lean --run tests/regression/inflate-deferred-distance/distance.lean \
    > "$work/lean.out" 2> "$work/lean.err"; then
  cat "$work/lean.out" "$work/lean.err" >&2; exit 1
fi
if [ "${SAN:-0}" = 1 ]; then
  if ! env -u LSAN_OPTIONS ASAN_OPTIONS=detect_leaks=1:halt_on_error=1 \
      UBSAN_OPTIONS=halt_on_error=1 "$work/distance-c" > "$work/c.out" 2> "$work/c.err"; then
    cat "$work/c.err" >&2; exit 1
  fi
else
  if ! "$work/distance-c" > "$work/c.out" 2> "$work/c.err"; then
    cat "$work/c.err" >&2; exit 1
  fi
fi
if [ -s "$work/c.err" ] || [ -s "$work/lean.err" ]; then
  cat "$work/c.err" "$work/lean.err" >&2; exit 1
fi
if [ "$(wc -l < "$work/c.out")" -ne 3 ] || [ "$(wc -l < "$work/lean.out")" -ne 3 ]; then
  echo "expected three observed-state rows" >&2; exit 1
fi
cmp "$work/c.out" "$work/lean.out"
grep -Fq 'first rc=0 used=3 produced=1 avail_in=1 avail_out=0' "$work/c.out"
grep -Fq 'second rc=-3 used=3 produced=1 avail_in=1 avail_out=8' "$work/c.out"
[ "$(grep -Fc 'prefix=730442 output=41 ' "$work/c.out")" -eq 2 ]
grep -Fxq 'end rc=0 state_null=1' "$work/c.out"
echo "PASS: three C/Lean rows identical; consumed prefix and deferred error recorded ($variant)"
