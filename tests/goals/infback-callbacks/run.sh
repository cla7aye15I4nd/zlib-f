#!/usr/bin/env bash
# Statement test for the inflateBack safety goal: the real zlib (pinned, patched) with adversarial
# call-backs under AddressSanitizer, LeakSanitizer and UndefinedBehaviorSanitizer.
# Usage: run.sh [first-seed] [count]
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)
work=${WORK:-$(mktemp -d)}
san="-fsanitize=address,undefined -fno-sanitize-recover=undefined -fno-omit-frame-pointer -g -O1"
CFLAGS="$san" "$root/tests/build-zlib.sh" "$root/zlib" "$work/zlib" >/dev/null
cc $san -I"$work/zlib" "$here/harness.c" "$work/zlib/libz.a" -o "$work/harness"
leaks=0; [ "$(uname)" = Linux ] && leaks=1
ASAN_OPTIONS=detect_leaks=$leaks:abort_on_error=1 UBSAN_OPTIONS=print_stacktrace=1:halt_on_error=1 \
  "$work/harness" "${1:-1}" "${2:-20000}"
