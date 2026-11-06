#!/usr/bin/env bash
# Internal-state translation regression. Evidence, not a zlib API bug report.
set -euo pipefail
root=$(cd "$(dirname "$0")/../../.." && pwd)
cd "$root"
work="$root/tests/build/deflate-slide"
mkdir -p "$work"
zlib="${ZLIB_BUILD:-$root/tests/build/zlib}"
[ -f "$zlib/libz.a" ] || { echo "missing libz.a" >&2; exit 2; }
zlib=$(cd "$zlib" && pwd)
cc -O1 -g -Wall -Wextra -fsanitize=address,undefined -fno-sanitize-recover=undefined \
  -I"$zlib" tests/regression/deflate-slide/slide.c "$zlib/libz.a" -o "$work/slide-c" \
  > "$work/c-build.log" 2>&1
lake build 'ZlibF.Zlib.«deflate_base.c»' > "$work/lean-build.log" 2>&1
lake env lean --run tests/regression/deflate-slide/slide.lean > "$work/lean.out" 2> "$work/lean.err"
env -u LSAN_OPTIONS UBSAN_OPTIONS=halt_on_error=1 "$work/slide-c" > "$work/c.out" 2> "$work/c.err"
[ ! -s "$work/c.err" ] && [ ! -s "$work/lean.err" ]
[ "$(wc -l < "$work/c.out")" -eq 3 ]
[ "$(wc -l < "$work/lean.out")" -eq 4 ]
head -n 3 "$work/lean.out" > "$work/lean-defined.out"
cmp "$work/c.out" "$work/lean-defined.out"
tail -n 1 "$work/lean.out" | grep -Fxq 'UB: signed long overflow'
if env -u LSAN_OPTIONS UBSAN_OPTIONS=halt_on_error=1 "$work/slide-c" overflow \
    > "$work/overflow.out" 2> "$work/overflow.err"; then
  echo "expected the C internal-state overflow to be rejected by UBSan" >&2
  exit 1
fi
grep -Fq 'signed integer overflow' "$work/overflow.err"
grep -Fq 'deflate.c:' "$work/overflow.err"
python3 tests/regression/deflate-slide/selftest.py
echo 'PASS: three defined C/Lean slide states match; both detect the artificial signed-overflow state'
