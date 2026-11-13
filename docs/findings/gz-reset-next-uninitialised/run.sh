#!/usr/bin/env bash
# Usage: ZLIB_SRC=<zlib checkout> bash docs/findings/gz-reset-next-uninitialised/run.sh
# Builds the pinned zlib twice under ASan and UBSan: with patches/*.patch except 0005 (the
# source before the fix), and with all of patches/*.patch. In each copy, the "x.next += n"
# statements of gzlib.c and gzread.c are routed through the probe of probe.h (the value is
# unchanged). Runs unset.c on each. Before the fix the probe must see x.next evaluated with
# n == 0 on the never-written field (gzseek in gzlib.c, gz_skip_have in gzread.c); after the
# fix it must see no such evaluation. Neither build may get a sanitizer report: no sanitizer
# detects this, which is why the probe is used.
set -uo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$here/../../..
src=${ZLIB_SRC:?set ZLIB_SRC to the pinned zlib checkout}
work=${WORK:-$root/tests/build/gz-reset-next-uninitialised}
san="-fsanitize=address,undefined -fno-sanitize-recover=undefined -g -O1"
prog=${PROG:-unset}
progdir=${PROGDIR:-$here}
mkdir -p "$work/without/tests" "$work/without/patches"
cp "$root/tests/build-zlib.sh" "$work/without/tests/"
for p in "$root"/patches/*.patch; do
  case "$(basename "$p")" in 0005-*) ;; *) cp "$p" "$work/without/patches/";; esac
done
CFLAGS="$san" bash "$work/without/tests/build-zlib.sh" "$src" "$work/before" >/dev/null || exit 2
CFLAGS="$san" bash "$root/tests/build-zlib.sh" "$src" "$work/after" >/dev/null || exit 2
fail=0
for b in before after; do
  d=$work/$b
  sed -i.orig 's/state->x\.next += n;/state->x.next += ZPROBE_NEXT(state->x.next, n);/' "$d/gzlib.c" "$d/gzread.c"
  [ "$(grep -c ZPROBE_NEXT "$d/gzlib.c" "$d/gzread.c" | awk -F: '{s += $2} END {print s}')" -ge 4 ] ||
    { echo "probe not inserted"; exit 2; }
  (cd "$d" && make libz.a CFLAGS="$san -include $here/probe.h" >/dev/null) || exit 2
  cc $san -I"$d" "$progdir/$prog.c" "$d/libz.a" -o "$work/$prog-$b" || exit 2
  echo "== $b"
  out=$(cd "$work" && "$work/$prog-$b" 2>&1)
  printf '%s\n' "$out"
  if printf '%s\n' "$out" | grep -q "runtime error\|ERROR: AddressSanitizer"; then
    echo "UNEXPECTED: a sanitizer report"; fail=1
  elif [ $b = before ]; then
    if printf '%s\n' "$out" | grep -q "^x.next + 0 at gzlib.c" && printf '%s\n' "$out" | grep -q "^x.next + 0 at gzread.c"; then
      echo "ok: before the fix: x.next evaluated with n == 0 in gzseek64 and gz_skip_have"
    else
      echo "MISSING: no evaluation of x.next with n == 0"; fail=1
    fi
  else
    if printf '%s\n' "$out" | grep -q "^x.next + 0 at"; then
      echo "UNEXPECTED: x.next evaluated with n == 0 after the fix"; fail=1
    else
      echo "ok: after the fix: x.next is never evaluated with n == 0"
    fi
  fi
done
exit $fail
