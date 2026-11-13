#!/usr/bin/env bash
# Usage: ZLIB_SRC=<zlib checkout> bash tests/goals/deflate-quiet/run.sh
# Builds the patched zlib copy and replays gz_comp's deflate loop with no input (see driver.c).
# Exit 0: every loop ends for an output buffer of at least 8 bytes, and the known 1-byte case cycles.
# Evidence about the C behind DeflateQuiet (gz.skeleton-write.lean), not proof.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
src=${ZLIB_SRC:?set ZLIB_SRC to the pinned zlib checkout}
work=${WORK:-$here/../../build/goals-deflate-quiet}
mkdir -p "$work"
bash "$here/../../build-zlib.sh" "$src" "$work/z" >/dev/null
cc -O2 -I"$work/z" "$here/driver.c" "$work/z/libz.a" -o "$work/driver"
"$work/driver"
