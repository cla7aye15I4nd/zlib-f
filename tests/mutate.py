#!/usr/bin/env python3
"""mutate.py <file> <occurrence> <old> <new>: replace the <occurrence>-th (1-based) occurrence of the
text <old> in <file> by <new>. Fails if there are fewer occurrences, or if the text is unchanged."""
import sys
path, occ, old, new = sys.argv[1], int(sys.argv[2]), sys.argv[3], sys.argv[4]
s = open(path).read()
pos = -1
for _ in range(occ):
    pos = s.find(old, pos + 1)
    if pos < 0:
        sys.exit(f"mutate: {old!r} occurs fewer than {occ} times in {path}")
if old == new:
    sys.exit("mutate: old == new")
open(path, "w").write(s[:pos] + new + s[pos + len(old):])
