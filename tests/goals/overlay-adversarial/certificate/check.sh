#!/usr/bin/env bash
# Usage: ZLIB_SRC=<zlib checkout> bash tests/goals/overlay-adversarial/certificate/check.sh [ROUNDS] [SEEDS]
# Statement test of the memLevel 2 and memLevel 1 certificates on the real C (see check.c): builds the patched
# zlib copy, puts a hook after build_bl_tree in _tr_flush_block, compiles check.c with
# AddressSanitizer and UndefinedBehaviorSanitizer, replays the saved memLevel 2 block, and runs
# the search. Exit 0: every fact held on every block. Exit 1: a violated fact (the block is printed).
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
src=${ZLIB_SRC:?set ZLIB_SRC to the pinned zlib checkout}
rounds=${1:-200000}
seeds=${2:-4}
work=${WORK:-$here/../../../build/goals-overlay-certificate}
mkdir -p "$work"
bound=${BOUND:-}
if [ -z "$bound" ]; then
  cc -O2 -o "$work/lpsolve" "$here/lpsolve.c"
  bound=$(LPSOLVE="$work/lpsolve" python3 "$here/overlay_cert.py" --bound)
fi
bash "$here/../../../build-zlib.sh" "$src" "$work/z" >/dev/null
python3 - "$work/z/trees.c" "$work/trees-hook.c" <<'PY'
import sys
s = open(sys.argv[1]).read()
costs = "        static_lenb = (s->static_len + 3 + 7) >> 3;\n"
head = "local void compress_block(deflate_state *s, const ct_data *ltree,"
for part in (costs, head):
    if s.count(part) != 1:
        sys.exit("certificate check: trees.c changed, hook point not found: " + part.splitlines()[0])
s = s.replace(costs, costs + "        if (g_hook2) g_hook2(s);\n")
s = s.replace(head, "void (*g_hook2)(deflate_state *);\n" + head)
open(sys.argv[2], "w").write(s)
PY
z=$work/z
cc -O1 -g -fsanitize=address,undefined -fno-sanitize-recover=undefined -w -DBOUND="$bound" -I"$z" \
  -o "$work/check" "$here/check.c" "$z/adler32.c" "$z/crc32.c" "$z/deflate.c" "$z/zutil.c" "$work/trees-hook.c" -lm
status=0
for case in "$here"/../cases/memlevel2-*.txt; do "$work/check" replay "$case" || status=1; done
for seed in $(seq 1 "$seeds"); do "$work/check" search "$rounds" "$seed" 2>/dev/null || status=1; done
for case in "$here"/../cases/memlevel1-*.txt; do MEMLEVEL=1 "$work/check" replay "$case" || status=1; done
for seed in $(seq 1 "$seeds"); do MEMLEVEL=1 "$work/check" search "$rounds" "$seed" 2>/dev/null || status=1; done
exit $status
