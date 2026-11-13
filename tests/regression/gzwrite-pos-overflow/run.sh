#!/usr/bin/env bash
# Usage: ZLIB_SRC=<zlib checkout> [FULL=1] bash tests/regression/gzwrite-pos-overflow/run.sh
# Builds the pinned zlib twice under UBSan: with patches/*.patch except 0004 (the source before
# the fix), and with all of patches/*.patch. Runs wpos.c on each: a transparent writer on
# /dev/null seeks to INT64_MAX - 10 and writes 100 bytes, and (argument "putc") seeks to
# INT64_MAX and writes one byte with gzputc. Without 0004 each run must report a signed
# overflow of the position; with 0004 nothing may be reported, and the write must fail with
# Z_DATA_ERROR "position overflow".
# By default fastwrite.c answers the writes to /dev/null without a system call (about a minute
# per run). FULL=1 uses the real /dev/null: about 17 minutes per run on x86_64 Linux, so about an
# hour in all. Both modes build with UBSan only: under ASan the 2^34 intercepted writes take hours.
set -uo pipefail
here=$(cd "$(dirname "$0")" && pwd)
src=${ZLIB_SRC:?set ZLIB_SRC to the pinned zlib checkout}
work=${WORK:-$here/../../build/gzwrite-pos-overflow}
san="-fsanitize=undefined -fno-sanitize-recover=undefined -g -O2"
if [ "${FULL:-0}" = 1 ]; then extra=""; else extra="$here/fastwrite.c"; fi
libs=""; [ "$(uname -s)" = Linux ] && libs="-ldl"
mkdir -p "$work/without/tests" "$work/without/patches"
cp "$here/../../build-zlib.sh" "$work/without/tests/"
for p in "$here"/../../../patches/*.patch; do
  case "$(basename "$p")" in 0004-*) ;; *) cp "$p" "$work/without/patches/";; esac
done
CFLAGS="$san" bash "$work/without/tests/build-zlib.sh" "$src" "$work/before" >/dev/null || exit 2
CFLAGS="$san" bash "$here/../../build-zlib.sh" "$src" "$work/after" >/dev/null || exit 2
fail=0
for b in before after; do
  cc $san -I"$work/$b" "$here/wpos.c" $extra "$work/$b/libz.a" $libs -o "$work/wpos-$b" || exit 2
  for mode in write putc; do
    echo "== $b $mode"
    out=$("$work/wpos-$b" $mode 2>&1)
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
