#!/usr/bin/env bash
# Usage: ZLIB_SRC=<zlib checkout> bash tests/goals/compress-safety/run.sh [RUNS] [SEED]
# Builds the patched zlib copy with sanitizers and checks the compress* safety clauses on
# random inputs (see driver.c). Exit 0: no clause violated on these inputs. Evidence, not proof.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
src=${ZLIB_SRC:?set ZLIB_SRC to the pinned zlib checkout}
work=${WORK:-$here/../../build/goals-compress-safety}
mkdir -p "$work"
CFLAGS="-O1 -g -fsanitize=address,undefined -fno-sanitize-recover=undefined" \
  bash "$here/../../build-zlib.sh" "$src" "$work/z" >/dev/null
cc -O1 -g -fsanitize=address,undefined -fno-sanitize-recover=undefined -I"$work/z" "$here/driver.c" \
  "$work/z/libz.a" -Wl,--wrap=malloc,--wrap=free -o "$work/driver"
"$work/driver" "${2:-1}" "${1:-2000}"
