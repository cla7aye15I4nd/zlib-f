#!/usr/bin/env bash
# Usage: ZLIB_SRC=<zlib checkout> bash tests/regression/gzseek-pushback-overflow/run.sh
# Builds the pinned zlib twice under ASan and UBSan: once without any patch (the unpatched source)
# and once with patches/*.patch (the verified source, which includes 0002). Runs seek.c on a
# transparent file and on a gzip file, with SEEK_CUR and SEEK_SET after an initial gzungetc.
# The unpatched build must report a signed overflow in gzseek64 for each of the four runs; the
# patched build must report nothing, and every seek must return -1 (SEEK_SET) or 0 (SEEK_CUR).
set -uo pipefail
here=$(cd "$(dirname "$0")" && pwd)
src=${ZLIB_SRC:?set ZLIB_SRC to the pinned zlib checkout}
work=${WORK:-$here/../../build/gzseek-pushback-overflow}
san="-fsanitize=address,undefined -fno-sanitize-recover=undefined -g -O1"
mkdir -p "$work"
# unpatched: an empty patch directory
mkdir -p "$work/nopatch/tests" "$work/nopatch/patches"
cp "$here/../../build-zlib.sh" "$work/nopatch/tests/"
CFLAGS="$san" bash "$work/nopatch/tests/build-zlib.sh" "$src" "$work/unpatched" >/dev/null || exit 2
CFLAGS="$san" bash "$here/../../build-zlib.sh" "$src" "$work/patched" >/dev/null || exit 2
printf abc > "$work/raw.dat"
printf abc | gzip -c > "$work/data.gz"
fail=0
for b in unpatched patched; do
  cc $san -I"$work/$b" "$here/seek.c" "$work/$b/libz.a" -o "$work/seek-$b" || exit 2
  for input in raw.dat data.gz; do
    for mode in cur set; do
      echo "== $b $input $mode"
      out=$(cd "$work/$b" && "$work/seek-$b" "$work/$input" $mode 2>&1)
      printf '%s\n' "$out" | sed "s#$work/##g"
      if [ $b = unpatched ]; then
        if printf '%s\n' "$out" | grep -q "runtime error: signed integer overflow"; then
          echo "ok: unpatched: signed overflow in gzseek64"
        else
          echo "MISSING: no signed overflow"; fail=1
        fi
      else
        want="seek set LONG_MAX = -1"; [ $mode = cur ] && want="seek cur 1 = 0"
        if printf '%s\n' "$out" | grep -q "runtime error\|ERROR: AddressSanitizer"; then
          echo "UNEXPECTED: a sanitizer report with the patch"; fail=1
        elif printf '%s\n' "$out" | grep -qx "$want"; then
          echo "ok: patched: $want, no report"
        else
          echo "UNEXPECTED: patched result"; fail=1
        fi
      fi
    done
  done
done
exit $fail
