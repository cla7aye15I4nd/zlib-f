#!/usr/bin/env bash
# Usage: ZLIB_SRC=<zlib checkout> bash tests/goals/overlay/run.sh [STEPS] [SEED]
# Builds the patched zlib copy (tests/build-zlib.sh), instruments its trees.c to record the gap
# between pending output and the next unread symbol in compress_block, and searches dynamic
# blocks at memLevel 1 to 4 for a negative gap (an overwritten symbol). Exit 0: none found.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
src=${ZLIB_SRC:?set ZLIB_SRC to the pinned zlib checkout}
steps=${1:-300000}
seed=${2:-1}
work=${WORK:-$here/../../build/goals-overlay}
mkdir -p "$work"
bash "$here/../../build-zlib.sh" "$src" "$work/z" >/dev/null
python3 - "$work/z/trees.c" "$work/trees-overlay.c" <<'PY'
import sys
s = open(sys.argv[1]).read()
start = "    if (s->sym_next != 0) do {\n#ifdef LIT_MEM"
check = '        Assert(s->pending < s->lit_bufsize + sx, "pendingBuf overflow");'
head = "local void compress_block(deflate_state *s, const ct_data *ltree,"
for part in (start, check, head):
    if s.count(part) != 1:
        sys.exit("overlay: trees.c changed, instrumentation point not found: " + part.splitlines()[0])
s = s.replace(start, "    { long m = (long)s->lit_bufsize - (long)s->pending; if (m < g_margin) g_margin = m; }\n" + start)
s = s.replace(check, "        { long m = (long)s->lit_bufsize + (long)sx - (long)s->pending;"
                     " if (m < g_margin) g_margin = m; }")
s = s.replace(head, "long g_margin;\n" + head)
open(sys.argv[2], "w").write(s)
PY
z=$work/z
cc -O2 -w -I"$z" -o "$work/search" "$here/search.c" "$z/adler32.c" "$z/crc32.c" "$z/deflate.c" \
  "$z/zutil.c" "$work/trees-overlay.c"
status=0
for memory in 1 2 3 4; do
  (cd "$work" && ./search "$memory" 15 "$steps" "$((seed + memory))" 2>/dev/null) || status=1
done
exit $status
