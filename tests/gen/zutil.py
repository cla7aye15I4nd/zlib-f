#!/usr/bin/env python3
"""Inputs for the zutil.c differential test, written to stdout. Deterministic.
Lines: zlibVersion | zlibCompileFlags | zError <int> | zcalloc_free <items> <size> | malloc <n>
zError is tried on every code in -12..12 (the documented -6..2 and both sides of it), at the
boundaries -7/3 of the table, and at INT_MIN, INT_MAX and a few large values.
zcalloc_free uses small products (each store of the Lean heap keeps the previous table alive, so memory is quadratic in the size) and one that wraps (2 * 2147483698 = 2^32 + 100) (the product is computed in unsigned).
malloc tries small sizes, which succeed, and sizes at and above PTRDIFF_MAX + 1 = 2^63 up to SIZE_MAX, which glibc
refuses whatever the memory state. Not tested: 2^63 - 1 and other huge sizes below the limit (the Lean side would build
the block; the C result depends on the memory, which the allocation oracle models)."""
import random

rng = random.Random(20261105)
out = ["zlibVersion", "zlibCompileFlags"]
for e in range(-12, 13):
    out.append("zError %d" % e)
for e in (-2**31, -2**31 + 1, -2**31 + 2, -1000, -100, 100, 1000, 2**31 - 2, 2**31 - 1):
    out.append("zError %d" % e)
out.append("zlibVersion")
for items, size in ((0, 0), (1, 0), (0, 5), (1, 1), (1, 7), (3, 5), (16, 16), (256, 2), (7, 60), (60, 7),
                    (2, 2147483698), (300, 2), (100, 4), (1, 500)):
    out.append("zcalloc_free %d %d" % (items, size))
for _ in range(40):
    out.append("zcalloc_free %d %d" % (rng.randrange(1, 25), rng.randrange(1, 25)))
for n in (0, 1, 4096, 2**63, 2**63 + 1, 2**64 - 1):
    out.append("malloc %d" % n)
print("\n".join(out))
