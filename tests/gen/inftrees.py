#!/usr/bin/env python3
"""Inputs for the inftrees.c differential test, written to stdout. Deterministic (fixed seed).

  inflate_table <type> <bits> <loff> <toff> <lens>     type: 0 CODES, 1 LENS, 2 DISTS; lens: one hex digit per symbol
  inflate_fixed
The code lengths cover: complete codes of every shape (random splits, skewed towards deep codes, lengths up
to 15, single and two symbols), incomplete codes, over-subscribed codes (one length changed, one symbol added or
removed), all-zero lengths, the single length-1 code (accepted for LENS and DISTS only), the fixed codes of
deflate, requested root sizes from 0 to 30 (below the shortest, above the longest, equal to both), and the
offsets of the lens and of the table inside their arrays, as the callers in inflate.c use them.
Bounds that the C needs: DISTS has at most 32 symbols (dbase and dext have 32 entries; a longer set with a code
length on a symbol above 31 reads past them); lens + loff stays in 320 entries, the table needs at most 852 (LENS), 592 (DISTS) entries
after toff in 1444; CODES uses lengths up to 7 only, as inflate.c does (3-bit code length code lengths).
"""
import random

rng = random.Random(20261105)
out = []

def complete(n, maxdepth, skew):
    """Lengths of a complete prefix code with n leaves (n >= 2), depths <= maxdepth."""
    leaves = [0]
    while len(leaves) < n:
        cand = [i for i, d in enumerate(leaves) if d < maxdepth]
        if not cand:
            break
        if skew and rng.randrange(3) > 0:
            m = max(leaves[i] for i in cand)
            cand = [i for i in cand if leaves[i] == m]
        i = rng.choice(cand)
        d = leaves.pop(i)
        leaves.insert(i, d + 1)
        leaves.insert(i, d + 1)
    return leaves

def place(lens, total):
    """Spread the lengths over `total` symbols; the others get length 0."""
    total = max(total, len(lens))
    pos = sorted(rng.sample(range(total), len(lens)))
    arr = [0] * total
    rng.shuffle(lens)
    for p, l in zip(pos, lens):
        arr[p] = l
    return arr

def hexs(arr):
    return "".join("%x" % v for v in arr) if arr else "-"

ROOTS = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 20, 30]

def emit(type_, bits, loff, toff, arr):
    out.append("inflate_table %d %d %d %d %s" % (type_, bits, loff, toff, hexs(arr)))

def emit_all_variants(type_, arr, roots):
    toffs = [0] if type_ == 1 else ([0, 852] if type_ == 2 else [0, 5])
    for b in roots:
        emit(type_, b, rng.choice([0, 0, 7, 286 - len(arr) if 286 - len(arr) >= 0 else 0]),
             rng.choice(toffs), arr)

def perturb(arr, maxlen):
    """Variants that are over-subscribed or incomplete."""
    res = []
    nz = [i for i, v in enumerate(arr) if v]
    z = [i for i, v in enumerate(arr) if not v]
    if nz:
        i = rng.choice(nz)
        a = list(arr); a[i] = min(maxlen, a[i] + 1); res.append(a)          # longer: incomplete (or equal)
        a = list(arr); a[i] = max(1, a[i] - 1); res.append(a)               # shorter: over-subscribed
        a = list(arr); a[i] = 0; res.append(a)                              # removed: incomplete
    if z:
        a = list(arr); a[rng.choice(z)] = rng.randrange(1, maxlen + 1); res.append(a)  # added
    return res

# 1. Deflate's fixed codes, as in inflate.c's old fixedtables: LENS root 9 over 288 symbols, DISTS root 5 over 32.
fixed_l = [8] * 144 + [9] * 112 + [7] * 24 + [8] * 8
fixed_d = [5] * 32
for b in (9, 5, 7, 8, 10, 15, 0):
    emit(1, b, 0, 0, fixed_l)
    emit(2, b, 0, 0, fixed_d)
out.append("inflate_fixed")

# 2. Edge sets.
emit(1, 9, 0, 0, [])                        # no symbols at all
emit(2, 6, 0, 0, [])
emit(0, 7, 0, 0, [])
for n in (1, 2, 5, 19, 100, 288):
    for t in (0, 1, 2):
        emit(t, 7 if t == 0 else 9 if t == 1 else 6, 0, 0, [0] * n)
for t in (0, 1, 2):
    for L in (1, 2, 3, 7, 8, 15):
        if t == 0 and L > 7:
            continue
        for n, pos in ((1, 0), (3, 2), (19, 18)):
            arr = [0] * n; arr[pos] = L
            for b in (0, 1, 6, 7, 9, 15):
                emit(t, b, 0, 0, arr)             # single code (accepted only if its length is 1, for LENS/DISTS)
for t in (1, 2):
    for n in (2, 3, 30, 31, 32, 286, 287, 288):
        if t == 2 and n > 32:
            continue          # a distance symbol above 31 reads beyond dbase/dext: undefined in C
        for pos in (0, n - 1):
            arr = [0] * n; arr[pos] = 1
            emit(t, 9, 0, 0, arr)
for t in (0, 1, 2):
    for n in (2, 4, 19):
        emit(t, 7, 0, 0, [1, 1] + [0] * (n - 2))         # two symbols of length 1: complete
        emit(t, 7, 0, 0, [1, 1, 1] + [0] * (n - 3) if n >= 3 else [1, 1])   # three of length 1: over-subscribed
        emit(t, 7, 0, 0, [2, 2, 2, 2] + [0] * (n - 4) if n >= 4 else [2, 2])  # four of length 2: complete

# 3. CODES (lengths 1..7, up to 19 symbols), complete, with perturbations.
for _ in range(220):
    n = rng.randrange(2, 20)
    lens = complete(n, 7, rng.randrange(2) == 0)
    arr = place(lens, 19 if rng.randrange(4) else rng.randrange(max(n, 2), 20))
    for b in (7, rng.choice(ROOTS[:9])):
        emit(0, b, rng.choice([0, 0, 5]), rng.choice([0, 3]), arr)
    for a in perturb(arr, 7):
        emit(0, 7, 0, 0, a)

# 4. LENS: complete codes with up to 288 symbols (length up to 15), many shapes, several roots.
for _ in range(330):
    n = rng.choice([2, 3, 4, 5, 8, 16, 30, 100, 200, 256, 280, 286, 288, rng.randrange(2, 289)])
    n = min(n, 288)
    total = rng.choice([286, 288, max(n, 257)]) if n <= 286 else 288
    lens = complete(n, 15, rng.randrange(2) == 0)
    arr = place(lens, max(total, n))
    b = rng.choice([9, 9, 9, 8, 10, 5, rng.choice(ROOTS)])
    emit(1, b, rng.choice([0, 0, 7]), rng.choice([0, 0, 100, 592]), arr)
    if rng.randrange(3) == 0:
        for a in perturb(arr, 15):
            emit(1, 9, 0, 0, a)
# Deep codes (length up to 15 with many symbols at depth 15/14/13: sub-tables of several sizes).
for depth_max in (10, 11, 12, 13, 14, 15):
    for _ in range(25):
        n = rng.randrange(16, 289)
        lens = complete(n, depth_max, True)
        arr = place(lens, 288)
        for b in (9, 8, 6, 12):
            emit(1, b, 0, 0, arr)

# 5. DISTS: complete codes with up to 32 symbols (30 valid), lengths up to 15, several roots, offsets as in inflate.c.
for _ in range(320):
    n = rng.choice([2, 3, 4, 5, 8, 16, 20, 30, 31, 32, rng.randrange(2, 33)])
    lens = complete(n, 15, rng.randrange(2) == 0)
    arr = place(lens, rng.choice([30, 32, max(n, 30)]))
    b = rng.choice([6, 6, 6, 5, 7, 4, rng.choice(ROOTS)])
    emit(2, b, rng.choice([0, 0, 286, 257]), rng.choice([0, 0, 100, 852]), arr)
    if rng.randrange(3) == 0:
        for a in perturb(arr, 15):
            emit(2, 6, 0, 0, a)

# 6. Space limit: sets that need more table entries than ENOUGH_LENS / ENOUGH_DISTS for a given root
#    (the code returns 1), tried with large roots and many sub-tables.
for _ in range(60):
    n = rng.randrange(150, 289)
    arr = place(complete(n, 15, True), 288)
    for b in (15, 14, 11, 10):
        emit(1, b, 0, 0, arr)
for _ in range(60):
    n = rng.randrange(16, 33)
    arr = place(complete(n, 15, True), 32)
    for b in (15, 14, 11, 10, 9):
        emit(2, b, 0, 0, arr)

# 7. Every root request on one code of each type (root below the shortest, inside, above the longest).
for t, lens_, total in ((1, complete(40, 12, True), 288), (2, complete(25, 13, True), 32), (0, complete(12, 7, True), 19)):
    arr = place(lens_, total)
    for b in ROOTS:
        if t == 0 and b > 7:
            continue
        emit(t, b, 0, 0, arr)

print("\n".join(out))
