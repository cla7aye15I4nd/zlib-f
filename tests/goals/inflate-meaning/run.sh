#!/usr/bin/env bash
# Usage: ZLIB_SRC=<zlib checkout> bash tests/goals/inflate-meaning/run.sh [SESSIONS] [SEED]
# Builds the patched zlib copy and the driver, and checks the stream-side facts of ParseMeaning on
# random protocol histories of the real C. Exit 0: no fact violated on these histories.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
src=${ZLIB_SRC:?set ZLIB_SRC to the pinned zlib checkout}
n=${1:-400}
seed=${2:-1}
work=${WORK:-$here/../../build/goals-inflate-meaning}
mkdir -p "$work"
bash "$here/../../build-zlib.sh" "$src" "$work/z" >/dev/null
cc -O2 -Wall -Wextra -I"$work/z" "$here/driver.c" "$work/z/libz.a" -o "$work/driver"
"$work/driver" "$seed" "$n" | python3 "$here/check.py"
