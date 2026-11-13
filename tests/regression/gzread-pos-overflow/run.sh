#!/usr/bin/env bash
# Usage: ZLIB_SRC=<zlib checkout> bash tests/regression/gzread-pos-overflow/run.sh
# Linux only: it needs a /dev/zero on which lseek succeeds without moving. Builds the pinned
# zlib twice under ASan and UBSan: with patches/*.patch except 0004 (the source before the fix),
# and with all of patches/*.patch. Runs devzero.c twice on each: a seek to INT64_MAX then a
# 16-byte gzread; a seek to INT64_MAX - 4 then gzread, the gzgetc() macro and gzgets; and a seek
# to INT64_MAX - 2 then gzungetc, the gzgetc() macro and function, gzdirect, gzseek and gzgets.
# Without 0004 each run must report a signed overflow of the position; with 0004 nothing may
# be reported, and the reads must stop with Z_DATA_ERROR "position overflow".
set -uo pipefail
here=$(cd "$(dirname "$0")" && pwd)
src=${ZLIB_SRC:?set ZLIB_SRC to the pinned zlib checkout}
work=${WORK:-$here/../../build/gzread-pos-overflow}
san="-fsanitize=address,undefined -fno-sanitize-recover=undefined -g -O1"
[ "$(uname -s)" = Linux ] || { echo "skip: needs Linux (/dev/zero with a succeeding lseek)"; exit 0; }
mkdir -p "$work/without/tests" "$work/without/patches"
cp "$here/../../build-zlib.sh" "$work/without/tests/"
for p in "$here"/../../../patches/*.patch; do
  case "$(basename "$p")" in 0004-*) ;; *) cp "$p" "$work/without/patches/";; esac
done
CFLAGS="$san" bash "$work/without/tests/build-zlib.sh" "$src" "$work/before" >/dev/null || exit 2
CFLAGS="$san" bash "$here/../../build-zlib.sh" "$src" "$work/after" >/dev/null || exit 2
fail=0
for b in before after; do
  cc $san -I"$work/$b" "$here/devzero.c" "$work/$b/libz.a" -o "$work/devzero-$b" || exit 2
  for mode in max near fast; do
    echo "== $b $mode"
    out=$("$work/devzero-$b" $mode 2>&1)
    printf '%s\n' "$out" | sed "s#$work/##g; s#$here/##g"
    if [ $b = before ]; then
      if printf '%s\n' "$out" | grep -q "runtime error: signed integer overflow"; then
        echo "ok: before the fix: signed overflow of the position"
      else
        echo "MISSING: no signed overflow"; fail=1
      fi
    else
      if printf '%s\n' "$out" | grep -q "runtime error\|ERROR: AddressSanitizer"; then
        echo "UNEXPECTED: a sanitizer report with the fix"; fail=1
      elif printf '%s\n' "$out" | grep -q "err = -3 (.*position overflow)"; then
        echo "ok: with the fix: Z_DATA_ERROR position overflow, no report"
      else
        echo "UNEXPECTED: result with the fix"; fail=1
      fi
    fi
  done
done
exit $fail
