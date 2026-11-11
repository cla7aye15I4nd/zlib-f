#!/usr/bin/env bash
# Usage: ZLIB_SRC=<zlib checkout> bash tests/goals/deflate/run.sh [SESSIONS] [SEED]
# Builds the patched zlib copy (tests/build-zlib.sh), the driver, and checks the clauses of the
# deflate goals on random histories of the real C: once plainly, once focused on the tight
# deflateBound cases, once under ASan and UBSan. Exit 0: no clause violated on these histories.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
src=${ZLIB_SRC:?set ZLIB_SRC to the pinned zlib checkout}
n=${1:-400}
seed=${2:-1}
work=${WORK:-$here/../../build/goals-deflate}
mkdir -p "$work"
bash "$here/../../build-zlib.sh" "$src" "$work/z" >/dev/null
CFLAGS="-fsanitize=address,undefined -fno-sanitize-recover=all -g -O1" \
  bash "$here/../../build-zlib.sh" "$src" "$work/zs" >/dev/null
cc -O2 -Wall -Wextra -I"$work/z" "$here/driver.c" "$work/z/libz.a" -o "$work/driver"
cc -O1 -g -fsanitize=address,undefined -fno-sanitize-recover=all -I"$work/zs" "$here/driver.c" \
  "$work/zs/libz.a" -o "$work/driver-san"
"$work/driver" "$seed" "$n" | python3 "$here/check.py"
"$work/driver" "$((seed + 1))" "$n" 1 | python3 "$here/check.py"
"$work/driver-san" "$((seed + 2))" "$((n / 4 + 1))" | python3 "$here/check.py"
