#!/usr/bin/env bash
# Usage: ZLIB_SRC=<zlib checkout> bash tests/goals/overlay-adversarial/run.sh [ROUNDS] [SEEDS]
# Builds the patched zlib copy (tests/build-zlib.sh), instruments its trees.c to record the gap
# between pending output and the next unread symbol in compress_block (as tests/goals/overlay),
# compiles adversarial.c with AddressSanitizer and UndefinedBehaviorSanitizer, replays the saved
# tightest blocks in cases/, then runs the targeted search at memLevel 1 and 2.
# Exit 0: no overwritten symbol. Exit 1: a negative gap (the block is printed).
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
src=${ZLIB_SRC:?set ZLIB_SRC to the pinned zlib checkout}
rounds=${1:-300000}
seeds=${2:-2}
work=${WORK:-$here/../../build/goals-overlay-adversarial}
mkdir -p "$work"
bash "$here/../../build-zlib.sh" "$src" "$work/z" >/dev/null
python3 - "$work/z/trees.c" "$work/trees-overlay.c" <<'PY'
import sys
s = open(sys.argv[1]).read()
start = "    if (s->sym_next != 0) do {\n#ifdef LIT_MEM"
check = '        Assert(s->pending < s->lit_bufsize + sx, "pendingBuf overflow");'
head = "local void compress_block(deflate_state *s, const ct_data *ltree,"
entry = "    int max_blindex = 0;  /* index of last bit length code of non zero freq */\n"
costs = "        static_lenb = (s->static_len + 3 + 7) >> 3;\n"
for part in (start, check, head, entry, costs):
    if s.count(part) != 1:
        sys.exit("overlay-adversarial: trees.c changed, instrumentation point not found: " + part.splitlines()[0])
s = s.replace(start, "    if (ltree == s->dyn_ltree && g_hook) g_hook(s);\n"
                     "    { long m = (long)s->lit_bufsize - (long)s->pending; if (m < g_margin) g_margin = m; }\n" + start)
s = s.replace(check, "        { long m = (long)s->lit_bufsize + (long)sx - (long)s->pending;"
                     " if (m < g_margin) g_margin = m; }")
s = s.replace(head, "long g_margin, g_entry; unsigned long g_opt, g_stat; void (*g_hook)(deflate_state *);\n" + head)
s = s.replace(entry, entry + "    g_entry = 8L * (long)s->pending + s->bi_valid;\n")
s = s.replace(costs, costs + "        g_opt = s->opt_len; g_stat = s->static_len;\n")
open(sys.argv[2], "w").write(s)
PY
z=$work/z
cc -O1 -g -fsanitize=address,undefined -fno-sanitize-recover=undefined -w -I"$z" -o "$work/adversarial" \
  "$here/adversarial.c" "$z/adler32.c" "$z/crc32.c" "$z/deflate.c" "$z/zutil.c" "$work/trees-overlay.c" -lm
status=0
for case in "$here"/cases/*.txt; do
  memory=1; case "$case" in *memlevel2*) memory=2;; esac
  "$work/adversarial" check "$memory" "$case" || status=1
done
for memory in 1 2; do
  for seed in $(seq 1 "$seeds"); do
    "$work/adversarial" search "$memory" "$rounds" "$seed" 2>/dev/null || status=1
  done
done
exit $status
