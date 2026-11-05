#!/usr/bin/env python3
"""Inputs for the inffast.c differential test, written to stdout. Deterministic (fixed seed).

  inflate_fast <tab> <wsize> <whave> <wnext> <hold> <bits> <avail_out> <window> <prior> <input>
(see tests/c/inffast.c). Entry assumptions of inflate_fast hold in every case: avail_in >= 6, avail_out >= 258,
start >= avail_out, bits < 8, hold < 2^bits, whave <= wsize, and the window is either filling (whave == wnext < wsize)
or full (whave == wsize, any wnext < wsize), as inflate() leaves it. sane is 1.

The input is built three ways: (a) a well-formed symbol sequence encoded with the code in use (literals, matches
with distances inside the prior output and the window, sometimes just beyond, an end-of-block at the end),
(b) the same with the bits of hold taken from its start, (c) random bytes (every error path: invalid codes of the
fixed tables, single-code dynamic tables, distances too far back).
Window paths covered: wnext == 0 (copy from the end of the window), wnext < op (wrap around), contiguous in the
window, window then output, output only (dist <= bytes written so far), dist == 1 (overlapping copy), lengths 3..258.
Table kinds: the fixed tables, random complete dynamic codes, and single-code tables (incomplete, with invalid entries).
"""
import random

rng = random.Random(20261105)
out = []

LBASE = [3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31, 35, 43, 51, 59, 67, 83, 99, 115, 131, 163, 195, 227, 258]
LEXT = [0] * 8 + [1] * 4 + [2] * 4 + [3] * 4 + [4] * 4 + [5] * 4 + [0]
DBASE = [1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193, 257, 385, 513, 769, 1025, 1537, 2049, 3073,
         4097, 6145, 8193, 12289, 16385, 24577]
DEXT = [0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12, 13, 13]

def complete(n, maxdepth, skew):
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

def place(lens, total, must=()):
    total = max(total, len(lens))
    pos = set(must)
    free = [p for p in range(total) if p not in pos]
    rng.shuffle(free)
    while len(pos) < len(lens):
        pos.add(free.pop())
    pos = sorted(pos)
    rng.shuffle(lens)
    arr = [0] * total
    for p, l in zip(pos, lens):
        arr[p] = l
    return arr

def canon(lens):
    """code value of each symbol (deflate canonical code), MSB first."""
    mx = max(lens) if lens else 0
    bl = [0] * (mx + 2)
    for l in lens:
        if l:
            bl[l] += 1
    nxt = [0] * (mx + 2)
    code = 0
    for b in range(1, mx + 1):
        code = (code + bl[b - 1]) << 1
        nxt[b] = code
    res = {}
    for s, l in enumerate(lens):
        if l:
            res[s] = (nxt[l], l)
            nxt[l] += 1
    return res

def code_bits(c):
    v, l = c
    return [(v >> (l - 1 - i)) & 1 for i in range(l)]

def val_bits(v, n):
    return [(v >> i) & 1 for i in range(n)]

def hexs(arr):
    return "".join("%x" % v for v in arr) if arr else "-"

def hexb(bs):
    return bytes(bs).hex() if len(bs) else "-"

FIXED_L = [8] * 144 + [9] * 112 + [7] * 24 + [8] * 8
FIXED_D = [5] * 32

def encode(lit, dist, maxdist, nsyms, with_eob):
    """Bits of a symbol sequence, using only symbols that have a code."""
    lc, dc = canon(lit), canon(dist)
    lits = [s for s in range(256) if s in lc]
    lensyms = [s for s in range(257, 286) if s in lc]
    dsyms = [d for d in range(30) if d in dc and DBASE[d] <= max(maxdist, 1)]
    bits = []
    for _ in range(nsyms):
        r = rng.randrange(100)
        if r < 45 and lits:
            bits += code_bits(lc[rng.choice(lits)])
        elif lensyms and dsyms:
            ls = rng.choice(lensyms)
            if rng.randrange(6) == 0:
                ls = rng.choice([lensyms[0], lensyms[-1]])
            bits += code_bits(lc[ls])
            le = rng.randrange(1 << LEXT[ls - 257])
            bits += val_bits(le, LEXT[ls - 257])
            ds = rng.choice(dsyms)
            if rng.randrange(5) == 0:
                ds = dsyms[0]
            bits += code_bits(dc[ds])
            de = rng.randrange(1 << DEXT[ds])
            if DBASE[ds] + de > maxdist and rng.randrange(12) != 0:
                de = max(0, min(de, maxdist - DBASE[ds]))
            bits += val_bits(de, DEXT[ds])
        elif lits:
            bits += code_bits(lc[rng.choice(lits)])
    if with_eob and 256 in lc:
        bits += code_bits(lc[256])
    return bits

def pack(bits):
    bs = bytearray((len(bits) + 7) // 8)
    for i, b in enumerate(bits):
        if b:
            bs[i // 8] |= 1 << (i % 8)
    return bytes(bs)

def window_params():
    wsize = rng.choice([0, 0, 256, 256, 512, 1024, 2048])
    if wsize == 0:
        return 0, 0, 0, b""
    if rng.randrange(2):
        whave = rng.randrange(0, wsize)
        wnext = whave
    else:
        whave = wsize
        wnext = rng.choice([0, 0, 1, wsize - 1, rng.randrange(wsize)])
    win = bytes(rng.randrange(256) for _ in range(wsize))
    return wsize, whave, wnext, win

def dyn_tables(kind):
    """(lit lens, dist lens) of a dynamic block header that inflate_table accepts (or the single-code cases)."""
    if kind == "single_dist":
        nl = rng.randrange(257, 287)
        lit = place(complete(rng.randrange(20, 120), 15, rng.randrange(2) == 0), nl, must=[256])
        dist = [0] * rng.randrange(1, 31)
        dist[rng.randrange(len(dist))] = 1
        return lit, dist
    if kind == "single_lit":
        nl = rng.randrange(257, 287)
        lit = [0] * nl
        lit[rng.choice([256, rng.randrange(nl)])] = 1
        dist = place(complete(rng.randrange(2, 30), 15, True), rng.randrange(2, 31))
        return lit, dist
    nl = rng.randrange(257, 287)
    nsym = rng.choice([rng.randrange(2, 40), rng.randrange(40, 287), 286, 150, 20])
    nsym = min(nsym, nl)
    lit = place(complete(nsym, 15, rng.randrange(2) == 0), nl, must=[256])
    nd = rng.randrange(2, 31)
    dist = place(complete(rng.randrange(2, nd + 1), 15, rng.randrange(2) == 0), nd)
    return lit, dist

def case(tab, lit, dist, wp, prior_len, avail_out, how, nsyms=None):
    wsize, whave, wnext, win = wp
    prior = bytes(rng.randrange(256) for _ in range(prior_len))
    bits = rng.randrange(8)
    maxdist = prior_len + whave
    if how == "enc":
        nsyms = nsyms if nsyms is not None else rng.choice([3, 10, 40, 150, 500])
        stream = encode(lit, dist, maxdist, nsyms, rng.randrange(2) == 0)
        # the first `bits` bits are in hold
        stream = stream + [rng.randrange(2) for _ in range(rng.randrange(0, 30))]
        while len(stream) < bits + 48:
            stream.append(rng.randrange(2))
        hold = sum(b << i for i, b in enumerate(stream[:bits]))
        inp = pack(stream[bits:])
        if len(inp) < 6:
            inp += bytes(6 - len(inp))
    else:
        hold = rng.randrange(1 << bits) if bits else 0
        inp = bytes(rng.randrange(256) for _ in range(rng.choice([6, 7, 8, 12, 20, 60, 300])))
    out.append("inflate_fast %s %d %d %d %d %d %d %s %s %s" %
               (tab, wsize, whave, wnext, hold, bits, avail_out, hexb(win), hexb(prior), inp.hex()))

def rand_avail():
    return rng.choice([258, 258, 259, 300, 400, 515, 600, 1000, 1500])

def rand_prior():
    return rng.choice([0, 0, 1, 2, 5, 40, 100, 257, 300])

for _ in range(500):
    case("fixed", FIXED_L, FIXED_D, window_params(), rand_prior(), rand_avail(), "enc")
for _ in range(500):
    lit, dist = dyn_tables("complete")
    case("dyn:%s:%s" % (hexs(lit), hexs(dist)), lit, dist, window_params(), rand_prior(), rand_avail(), "enc")
for _ in range(100):
    lit, dist = dyn_tables("single_dist")
    case("dyn:%s:%s" % (hexs(lit), hexs(dist)), lit, dist, window_params(), rand_prior(), rand_avail(), "enc")
for _ in range(100):
    lit, dist = dyn_tables("single_lit")
    case("dyn:%s:%s" % (hexs(lit), hexs(dist)), lit, dist, window_params(), rand_prior(), rand_avail(), "enc")
# random bytes: every error path
for _ in range(500):
    case("fixed", FIXED_L, FIXED_D, window_params(), rand_prior(), rand_avail(), "rand")
for _ in range(500):
    lit, dist = dyn_tables("complete")
    case("dyn:%s:%s" % (hexs(lit), hexs(dist)), lit, dist, window_params(), rand_prior(), rand_avail(), "rand")
for kind in ("single_dist", "single_lit"):
    for _ in range(60):
        lit, dist = dyn_tables(kind)
        case("dyn:%s:%s" % (hexs(lit), hexs(dist)), lit, dist, window_params(), rand_prior(), rand_avail(), "rand")
# long runs: the output limit (avail_out - 257) and the input limit (avail_in - 5) decide the end
for _ in range(100):
    case("fixed", FIXED_L, FIXED_D, window_params(), rand_prior(), 258, "enc", nsyms=400)
for _ in range(100):
    case("fixed", FIXED_L, FIXED_D, window_params(), rand_prior(), 20000 and 5000, "enc", nsyms=300)
# a window of 32768 bytes (the largest), full, with distances up to the whole window
for _ in range(6):
    wsize = 32768
    wnext = rng.choice([0, 1, 32767, rng.randrange(wsize)])
    win = bytes(rng.randrange(256) for _ in range(wsize))
    prior = bytes(rng.randrange(256) for _ in range(rng.choice([0, 10, 300])))
    nsyms = 200
    lit, dist = FIXED_L, FIXED_D
    stream = encode(lit, dist, wsize + len(prior), nsyms, True) + [rng.randrange(2) for _ in range(64)]
    bits = rng.randrange(8)
    hold = sum(b << i for i, b in enumerate(stream[:bits]))
    inp = pack(stream[bits:])
    out.append("inflate_fast fixed %d %d %d %d %d %d %s %s %s" %
               (wsize, wsize, wnext, hold, bits, 3000, win.hex(), hexb(prior), inp.hex()))

print("\n".join(out))
