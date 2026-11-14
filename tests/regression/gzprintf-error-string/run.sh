#!/usr/bin/env bash
# Usage: bash tests/regression/gzprintf-error-string/run.sh
# Builds the pinned zlib (the submodule) with patches/*.patch under ASan and runs errstr.c: a
# transparent writer on a full non-blocking pipe stalls (EAGAIN), gzerror returns the handle's
# message, and gzprintf(f, "%s", msg) frees that message (gz_error(state, Z_OK, NULL)) before
# vsnprintf reads it. The run must report a heap-use-after-free in gzvprintf.
# Set ZLIB_SRC to use another checkout of the pinned source.
set -uo pipefail
here=$(cd "$(dirname "$0")" && pwd)
src=${ZLIB_SRC:-$here/../../../zlib}
work=${WORK:-$here/../../build/gzprintf-error-string}
san="-fsanitize=address -g -O1"
mkdir -p "$work"
CFLAGS="$san" bash "$here/../../build-zlib.sh" "$src" "$work/z" >/dev/null || exit 2
cc $san -I"$work/z" "$here/errstr.c" "$work/z/libz.a" -o "$work/errstr" || exit 2
out=$("$work/errstr" 2>&1)
printf '%s\n' "$out" | sed "s#$work/##g; s#$here/##g"
if printf '%s\n' "$out" | grep -q "heap-use-after-free"; then
  echo "ok: heap-use-after-free of the handle's message"
  exit 0
fi
echo "MISSING: no use-after-free"
exit 1
