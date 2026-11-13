#!/usr/bin/env bash
# Evidence for a loop invariant of the inflateBack safety proof: when inflateBack takes the fast
# path (have >= 6 && left >= 258), fewer than 8 bits are held. inflate_fast documents this as an
# entry assumption (state->bits < 8); inflate.c checks it, infback.c does not. A copy of the
# patched zlib traps when the fast path starts with bits >= 8; the harness of run.sh drives it.
# Usage: bits8.sh [first-seed] [count]
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)
work=${WORK:-$(mktemp -d)}
rm -rf "$work/src" && mkdir -p "$work/src"
(cd "$root/zlib" && tar --exclude=.git -cf - .) | tar -C "$work/src" -xf -
python3 - "$work/src/infback.c" <<'PY'
import sys
f = sys.argv[1]; s = open(f).read()
a = "                RESTORE();\n                inflate_fast(strm, state->wsize);"
assert s.count(a) == 1, "fast path of infback.c not found"
s = s.replace(a, "                if (bits >= 8) __builtin_trap();\n" + a)
open(f, "w").write(s)
PY
san="-fsanitize=address,undefined -fno-sanitize-recover=undefined -fno-omit-frame-pointer -g -O1"
CFLAGS="$san" "$root/tests/build-zlib.sh" "$work/src" "$work/zlib" >/dev/null
cc $san -I"$work/zlib" "$here/harness.c" "$work/zlib/libz.a" -o "$work/harness"
ASAN_OPTIONS=detect_leaks=0:abort_on_error=1 UBSAN_OPTIONS=print_stacktrace=1:halt_on_error=1 \
  "$work/harness" "${1:-1}" "${2:-20000}"
