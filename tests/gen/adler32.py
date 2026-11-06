#!/usr/bin/env python3
"""Inputs for the adler32.c differential test, written to stdout.

Deterministic: fixed seed, no clock, no environment. Lines:
  adler32_z <adler> <buf>            adler32 <adler> <buf>
  adler32_combine <a1> <a2> <len2>   adler32_combine64 <a1> <a2> <len2>
with <buf> = null:<len> | hex:<digits> (see tests/README.md).
"""
import random

rng = random.Random(20261105)
BASE = 65521
NMAX = 5552
M64 = (1 << 64) - 1

out = []

def hexbuf(bs):
    return "hex:" + bytes(bs).hex()

def kind_bytes(kind, n):
    if kind == "zero":
        return bytes(n)
    if kind == "ff":
        return b"\xff" * n
    if kind == "ramp":
        return bytes((i * 7 + 3) & 0xff for i in range(n))
    return bytes(rng.randrange(256) for _ in range(n))

def pack(lo, hi):
    return lo | (hi << 16)

# Initial values: canonical, non-canonical (a half equal to or above BASE, or bits above 32).
INITS = [
    1, 0, 2, 0xffff, 0x10000, 0xffffffff, 0xffff0000,
    pack(BASE, BASE), pack(BASE - 1, BASE - 1), pack(BASE, 0), pack(0, BASE),
    pack(BASE + 1, BASE + 1), pack(0xfffe, 0xfffe),
    M64, 1 << 32, (1 << 63) | 1, 0x123456789abcdef0, 0xdeadbeef00000001,
]

def rand_init():
    r = rng.randrange(4)
    if r == 0:
        return rng.randrange(1 << 32)
    if r == 1:
        return rng.randrange(1 << 64)
    if r == 2:
        return pack(rng.randrange(BASE), rng.randrange(BASE))
    return pack(BASE - 1 - rng.randrange(3), BASE - 1 - rng.randrange(3))

# Lengths: every length up to 40, then around every constant in the code (16, NMAX, NMAX/16 steps)
# and around multiples of NMAX, and a couple of large ones.
LENS = set(range(0, 41))
for c in (47, 48, 49, 63, 64, 65, 255, 256, 257, 1000, 5535, 5536, 5537,
          NMAX - 17, NMAX - 16, NMAX - 15, NMAX - 2, NMAX - 1, NMAX, NMAX + 1, NMAX + 2,
          NMAX + 15, NMAX + 16, NMAX + 17, NMAX + 31, NMAX + 32, NMAX + 33,
          2 * NMAX - 1, 2 * NMAX, 2 * NMAX + 1, 2 * NMAX + 16, 3 * NMAX - 1, 3 * NMAX,
          3 * NMAX + 1, 3 * NMAX + 15, 20000, 65521 // 2):
    LENS.add(c)
LENS = sorted(LENS)

def emit_buf_cases(fn, lens, kinds, inits_per_case):
    for n in lens:
        for kind in kinds:
            data = kind_bytes(kind, n)
            ins = []
            if inits_per_case >= 4:
                ins = list(INITS)
            else:
                ins = [1, rng.choice(INITS)] + [rand_init() for _ in range(inits_per_case - 2)]
            for a in ins:
                out.append(f"{fn} {a} {hexbuf(data)}")

# 1. Small lengths: every kind, every special initial value (this covers the len == 1 and len < 16
#    paths and the 16 byte step).
for fn in ("adler32_z", "adler32"):
    emit_buf_cases(fn, [n for n in LENS if n <= 40], ("zero", "ff", "ramp", "rand"), 4)

# 2. Larger lengths around the constants, few initial values each (long lines).
for fn in ("adler32_z", "adler32"):
    emit_buf_cases(fn, [n for n in LENS if n > 40], ("zero", "ff", "ramp", "rand"), 3)

# 3. Boundary sums. With initial halves at BASE-1 and bytes 0xff the running sums are as large as the
#    modular reductions allow, in every position of the 5552 byte block.
FF = {n: b"\xff" * n for n in (1, 2, 3, 15, 16, 17, NMAX - 1, NMAX, NMAX + 1, 2 * NMAX)}
for fn in ("adler32_z", "adler32"):
    for n in sorted(FF):
        for lo in (BASE - 1, BASE - 2, 0xffff):
            for hi in (BASE - 1, 0, 0xffff):
                out.append(f"{fn} {pack(lo, hi)} {hexbuf(FF[n])}")

# 4. len == 1: reduction of `adler + b` and of `sum2 + adler` right at BASE (one below, equal,
#    one above), for several bytes. Initial halves may be non-canonical (up to 0xffff).
for fn in ("adler32_z", "adler32"):
    for b in (0, 1, 2, 3, 127, 128, 254, 255, rng.randrange(256), rng.randrange(256)):
        for lo in set(max(0, min(0xffff, BASE - b + d)) for d in (-2, -1, 0, 1, 2)) | {0, 1, 0xffff}:
            new_adler = lo + b
            red = new_adler - BASE if new_adler >= BASE else new_adler
            for hi in set(max(0, min(0xffff, BASE - red + d)) for d in (-2, -1, 0, 1, 2)) | {0, 0xffff}:
                out.append(f"{fn} {pack(lo, hi)} {hexbuf([b])}")
    # Same for len < 16 (adler reduced once at the end, sum2 by modulo).
    for n in range(2, 16):
        for lo in (BASE - 1, BASE - 2, BASE, 0xffff):
            for hi in (BASE - 1, BASE, 0, 0xffff):
                out.append(f"{fn} {pack(lo, hi)} {hexbuf(kind_bytes('rand', n))}")

# 5. NULL buffers: the documented initial value, for every length, with any `adler`.
NULL_LENS = [0, 1, 2, 3, 15, 16, 17, NMAX - 1, NMAX, NMAX + 1, 1 << 20, (1 << 32) - 1]
for fn in ("adler32_z", "adler32"):
    for n in NULL_LENS:
        for a in (0, 1, 123, 0xffffffff, M64, pack(BASE, BASE), rand_init()):
            out.append(f"{fn} {a} null:{n}")
for n in ((1 << 32), (1 << 40), M64):
    for a in (0, 1, 123, M64):
        out.append(f"adler32_z {a} null:{n}")

# 6. Random buffers, random lengths (short with high probability), random initial values.
for fn in ("adler32_z", "adler32"):
    for _ in range(600):
        r = rng.randrange(10)
        if r < 5:
            n = rng.randrange(0, 70)
        elif r < 8:
            n = rng.randrange(0, 1200)
        elif r < 9:
            n = rng.randrange(NMAX - 40, 2 * NMAX + 40)
        else:
            n = rng.randrange(0, 20000)
        kind = rng.choice(("zero", "ff", "ramp", "rand", "rand", "rand"))
        out.append(f"{fn} {rand_init()} {hexbuf(kind_bytes(kind, n))}")

# 7. Combine. (a) all combinations of boundary values of the halves and of len2;
#    (b) random.
def halves():
    s = set()
    for x in (0, 1, 2, BASE // 2, BASE - 2, BASE - 1, BASE, BASE + 1, 0xfffe, 0xffff):
        s.add(x)
    return sorted(s)

LEN2 = [0, 1, 2, 3, 15, 16, BASE - 1, BASE, BASE + 1, 2 * BASE, 5552, 1 << 16, (1 << 31) - 1,
        1 << 31, (1 << 32) - 1, 1 << 32, (1 << 32) + 1, (1 << 62) + 12345, (1 << 63) - 1,
        -1, -2, -BASE, -(1 << 31), -(1 << 63)]

def pairs_with_sum(targets, vals):
    # pairs (x, y) of halves with x + y in targets
    res = []
    for t in targets:
        got = []
        for x in vals:
            y = t - x
            if 0 <= y <= 0xffff:
                got.append((x, y))
        rng.shuffle(got)
        res.extend(got[:3])
    return sorted(set(res))

LO_PAIR_SUMS = [0, 1, 2, BASE - 1, BASE, BASE + 1, 2 * BASE - 1, 2 * BASE, 2 * BASE + 1, 0x1fffe]
HI_PAIR_SUMS = [0, 1, 2, BASE - 1, BASE, BASE + 1, 2 * BASE - 1, 2 * BASE, 2 * BASE + 1, 0x1fffe]
LO_PAIRS = pairs_with_sum(LO_PAIR_SUMS, halves())
HI_PAIRS = pairs_with_sum(HI_PAIR_SUMS, halves())
for fn in ("adler32_combine", "adler32_combine64"):
    # exact boundary of the conditional subtractions: sum of the two low halves / high halves
    for (l1, l2) in LO_PAIRS:
        for (h1, h2) in HI_PAIRS:
            for l in (0, 1, BASE - 1, BASE, 12345, -1):
                out.append(f"{fn} {pack(l1, h1)} {pack(l2, h2)} {l}")
    # every boundary len2 with a few ordinary checksums
    for l in LEN2:
        for (a1, a2) in ((1, 1), (pack(BASE - 1, BASE - 1), pack(BASE - 1, BASE - 1)),
                         (pack(0xffff, 0xffff), pack(0xffff, 0xffff)), (M64, M64), (0, 0)):
            out.append(f"{fn} {a1} {a2} {l}")
    for _ in range(1500):
        l = rng.choice([rng.randrange(0, 100), rng.randrange(0, 1 << 20), rng.randrange(0, 1 << 63),
                        -rng.randrange(1, 1 << 63), rng.choice(LEN2)])
        out.append(f"{fn} {rand_init()} {rand_init()} {l}")

print("\n".join(out))
