#!/usr/bin/env bash
# Usage: ZLIB_SRC=<zlib checkout> bash tests/goals/inflate-meaning-body/run.sh [SESSIONS] [SEED]
# Builds the patched zlib copy and the state-dump driver, and checks the decoding-side clauses of
# the inflate format meaning on random histories of the real C. Also builds late-rejection.c.
# Exit 0: no clause violated on these histories.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
src=${ZLIB_SRC:?set ZLIB_SRC to the pinned zlib checkout}
n=${1:-400}
seed=${2:-1}
work=${WORK:-$here/../../build/goals-inflate-meaning-body}
mkdir -p "$work"
bash "$here/../../build-zlib.sh" "$src" "$work/z" >/dev/null
cc -O2 -Wall -Wextra -I"$work/z" "$here/driver.c" "$work/z/libz.a" -o "$work/driver"
cc -O2 -Wall -I"$work/z" "$here/../inflate-meaning/late-rejection.c" "$work/z/libz.a" -o "$work/late-rejection"
"$work/driver" "$seed" "$n" | python3 "$here/check.py"
"$work/late-rejection"
