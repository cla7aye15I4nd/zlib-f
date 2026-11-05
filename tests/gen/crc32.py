#!/usr/bin/env python3
"""Inputs for the crc32.c differential test, written to stdout.

Deterministic: fixed seed, no clock, no environment. Lines:
  crc32_z <crc> <buf>   crc32 <crc> <buf>
  crc32_combine <c1> <c2> <len2>   crc32_combine64 <c1> <c2> <len2>
  crc32_combine_gen <len2>   crc32_combine_gen64 <len2>   crc32_combine_op <c1> <c2> <op>
  get_crc_table
with <buf> = null:<len> | hex:<digits> | off:<k>:<digits> (see the C driver).
The braided path starts at len >= 47 (N*W+W-1) and works on blocks of 40 bytes (N*W); the byte loops
unroll by 8; the pointer alignment (k mod 8) decides how many bytes precede the word loop.
"""
import random

rng = random.Random(20261105)
M64 = (1 << 64) - 1
POLY = 0xedb88320
out = []

def hexbuf(bs):
    return "hex:" + bytes(bs).hex()

def offbuf(k, bs):
    return "off:%d:%s" % (k, bytes(bs).hex())

def kind_bytes(kind, n):
    if kind == "zero":
        return bytes(n)
    if kind == "ff":
        return b"\xff" * n
    if kind == "ramp":
        return bytes((i * 7 + 3) & 0xff for i in range(n))
    return bytes(rng.randrange(256) for _ in range(n))

CRCS = [0, 1, 0xffffffff, 0x80000000, 0xdeadbeef, 0x00000100, 0xffff0000,
        1 << 32, (1 << 32) | 1, M64, 0x123456789abcdef0, (1 << 63) | 0x7fffffff]

def rand_crc():
    r = rng.randrange(3)
    if r == 0:
        return rng.randrange(1 << 32)
    if r == 1:
        return rng.randrange(1 << 64)
    return rng.choice(CRCS)

# 1. Every length up to 140 (below, at and above 47, 87, 127 = N*W*k+W-1; multiples of 8; 40), all contents,
#    aligned buffers, both entry points.
for n in range(0, 141):
    for kind in ("zero", "ff", "ramp", "rand"):
        d = kind_bytes(kind, n)
        for crc in (0, rand_crc()):
            out.append("crc32_z %d %s" % (crc, hexbuf(d)))
        out.append("crc32 %d %s" % (rand_crc(), hexbuf(d)))

# 2. Every alignment 0..7 at lengths around the thresholds (the alignment loop consumes 0..7 bytes and
#    the braided path needs at least one 40-byte block afterwards; 47 - 7 = 40).
for k in range(8):
    for n in sorted(set(list(range(0, 20)) + list(range(36, 60)) + list(range(76, 100)) + list(range(116, 140))
                        + [160, 200, 255, 256, 257, 1000])):
        d = kind_bytes("rand", n)
        out.append("crc32_z %d %s" % (rand_crc(), offbuf(k, d)))
        out.append("crc32 %d %s" % (rand_crc(), offbuf(k, d)))

# 3. Larger inputs, various alignments, around multiples of 40, and long ones.
for n in (199, 200, 201, 239, 240, 241, 1023, 1024, 4095, 4096, 4097, 5000, 20000):
    for k in (0, 1, 3, 5, 7):
        d = kind_bytes("rand", n)
        out.append("crc32_z %d %s" % (rand_crc(), offbuf(k, d)))
for kind in ("zero", "ff", "ramp"):
    out.append("crc32_z %d %s" % (rand_crc(), hexbuf(kind_bytes(kind, 20000))))
    out.append("crc32 %d %s" % (rand_crc(), offbuf(3, kind_bytes(kind, 9999))))

# 4. NULL buffers: the documented initial value, for any crc and length.
for n in (0, 1, 7, 8, 46, 47, 48, 1 << 20, (1 << 32) - 1):
    for crc in (0, 1, 0xffffffff, M64, rand_crc()):
        out.append("crc32_z %d null:%d" % (crc, n))
        if n < (1 << 32):
            out.append("crc32 %d null:%d" % (crc, n))
for n in (1 << 32, 1 << 40, M64):
    out.append("crc32_z %d null:%d" % (rand_crc(), n))

# 5. Random buffers, random lengths, random alignment.
for _ in range(500):
    r = rng.randrange(10)
    n = rng.randrange(0, 100) if r < 6 else rng.randrange(0, 700) if r < 9 else rng.randrange(0, 6000)
    k = rng.randrange(8) if rng.randrange(2) else 0
    out.append("crc32_z %d %s" % (rand_crc(), offbuf(k, kind_bytes(rng.choice(("zero", "ff", "ramp", "rand", "rand")), n))))

# 6. The table.
out.append("get_crc_table")

# 7. combine_gen: every small length, around powers of two (the loop over the bits of n and the table
#    index k & 31 with k = 3 + bit), negative values, the extremes.
LENS2 = set(range(0, 300))
for e in range(1, 63):
    for d in (-2, -1, 0, 1, 2):
        LENS2.add((1 << e) + d)
LENS2 |= {(1 << 63) - 1, (1 << 62) + 12345, 0x5555555555555555, 0x3333333333333333}
for n in sorted(LENS2):
    out.append("crc32_combine_gen64 %d" % n)
    out.append("crc32_combine_gen %d" % n)
for n in (-1, -2, -(1 << 31), -(1 << 62), -(1 << 63)):
    out.append("crc32_combine_gen64 %d" % n)
    out.append("crc32_combine_gen %d" % n)

# 8. combine / combine64 / combine_op.
def rev_mul(a, b):
    """multmodp as in crc32.c, in Python (a != 0 with a low 32 bit set)."""
    m = 1 << 31
    p = 0
    while True:
        if a & m:
            p ^= b
            if (a & (m - 1)) == 0:
                break
        m >>= 1
        b = ((b >> 1) ^ POLY) if b & 1 else b >> 1
    return p

def x2n(n, k):
    p = 1 << 31
    x = [1 << 30]
    for _ in range(31):
        x.append(rev_mul(x[-1], x[-1]))
    while n:
        if n & 1:
            p = rev_mul(x[k & 31], p)
        n >>= 1
        k += 1
    return p

for n in list(range(0, 70)) + [127, 128, 1000, 65535, 1 << 20, (1 << 40) + 3, (1 << 62) + 5]:
    for _ in range(3):
        c1, c2 = rng.randrange(1 << 32), rng.randrange(1 << 32)
        out.append("crc32_combine64 %d %d %d" % (c1, c2, n))
        out.append("crc32_combine %d %d %d" % (c1, c2, n))
        op = x2n(n, 3)
        out.append("crc32_combine_op %d %d %d" % (c1, c2, op))
for n in (-1, -5, -(1 << 63)):
    out.append("crc32_combine64 1 2 %d" % n)
    out.append("crc32_combine 1 2 %d" % n)
for c1, c2 in ((0, 0), (M64, M64), (1 << 32, 1 << 33), (0xffffffff, 0)):
    for n in (0, 1, 8, 1000):
        out.append("crc32_combine64 %d %d %d" % (c1, c2, n))
        out.append("crc32_combine_op %d %d %d" % (c1, c2, x2n(n, 3)))
# op values: zero, small, random with a nonzero low half (a nonzero low half is required to terminate), high bits set.
out.append("crc32_combine_op 5 6 0")
out.append("crc32_combine_op 5 6 1")
out.append("crc32_combine_op 5 6 2147483648")
out.append("crc32_combine_op 5 6 4294967295")
for _ in range(60):
    op = rng.randrange(1, 1 << 32)
    if rng.randrange(3) == 0:
        op |= rng.randrange(1 << 32) << 32
    out.append("crc32_combine_op %d %d %d" % (rand_crc(), rand_crc(), op))

print("\n".join(out))
