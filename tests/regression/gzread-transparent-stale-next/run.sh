#!/usr/bin/env bash
# Usage: ZLIB_SRC=<zlib checkout> bash tests/regression/gzread-transparent-stale-next/run.sh
# Builds the pinned zlib twice under ASan and UBSan: once without any patch (the unpatched source)
# and once with patches/*.patch (the verified source, which includes 0003). Runs stale.c on a
# 128-byte raw file with a read() that returns one byte and then fails with EIO. The unpatched build
# must report a heap-buffer-overflow READ in gz_read; the patched build must report nothing, and
# gzread must return 1 with err Z_ERRNO (-1).
set -uo pipefail
here=$(cd "$(dirname "$0")" && pwd)
src=${ZLIB_SRC:?set ZLIB_SRC to the pinned zlib checkout}
work=${WORK:-$here/../../build/gzread-transparent-stale-next}
san="-fsanitize=address,undefined -fno-sanitize-recover=undefined -fno-omit-frame-pointer -g -O1"
mkdir -p "$work"
# unpatched: an empty patch directory
mkdir -p "$work/nopatch/tests" "$work/nopatch/patches"
cp "$here/../../build-zlib.sh" "$work/nopatch/tests/"
CFLAGS="$san" bash "$work/nopatch/tests/build-zlib.sh" "$src" "$work/unpatched" >/dev/null || exit 2
CFLAGS="$san" bash "$here/../../build-zlib.sh" "$src" "$work/patched" >/dev/null || exit 2
head -c 128 /dev/zero > "$work/raw.dat"
fail=0
for b in unpatched patched; do
  cc $san -I"$work/$b" "$here/stale.c" "$work/$b/libz.a" -o "$work/stale-$b" ${LDLIBS:-} || exit 2
  echo "== $b"
  out=$(cd "$work/$b" && "$work/stale-$b" "$work/raw.dat" 2>&1)
  printf '%s\n' "$out" | sed "s#$work/##g; s#$here/#tests/regression/gzread-transparent-stale-next/#g"
  if [ $b = unpatched ]; then
    if printf '%s\n' "$out" | grep -q "heap-buffer-overflow" && printf '%s\n' "$out" | grep -q "in gz_read"; then
      echo "ok: unpatched: gz_read copies from the stale x.next past the output buffer"
    else
      echo "MISSING: no heap-buffer-overflow in gz_read"; fail=1
    fi
  else
    if printf '%s\n' "$out" | grep -q "runtime error\|ERROR: AddressSanitizer"; then
      echo "UNEXPECTED: a sanitizer report with the patch"; fail=1
    elif printf '%s\n' "$out" | grep -q "after: n=1 have=0 next-offset=1 err=-1"; then
      echo "ok: patched: gzread returns the byte and keeps Z_ERRNO, no report"
    else
      echo "UNEXPECTED: patched result"; fail=1
    fi
  fi
done
exit $fail
