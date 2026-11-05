#!/usr/bin/env python3
"""Inputs for the trees.c differential test, written to stdout. Deterministic (fixed seed).

Lines (see tests/c/trees.c for the exact grammar):
  bi_reverse <code> <len>                          sendbits <bi_buf> <bi_valid> <pend0> <v:l,...>
  bitop <windup|flush|flushbits|align> <bi_buf> <bi_valid> <pend0>
  stored <bi_buf> <bi_valid> <pend0> <last> <ramp|null> <len>
  detect <i:f,a-b:f,...>                           gen_codes <max_code> <16 bl_count> <i:len,...>
  buildtree <l|d|bl> <opt_len> <static_len> <i:freq,...>
  trees <lmax> <llens> <dmax> <dlens> <bi_buf> <bi_valid> <pend0>
  block <level> <strategy> <data_type> <bi_buf> <bi_valid> <lit_bufsize> <stored_len> <ramp|null> <last> <syms>
  tally <lit_bufsize> <syms>                       init
with <syms> = l<lc>[*n] | m<dist>:<lc>[*n], comma separated, or '-'.
Undefined behaviour of the C is never generated (match distance <= 32768, match lc <= 255, bi_valid 0..16 where
a shift by a negative count would follow, bit lengths <= 15 for gen_codes).
"""
import random

rng = random.Random(20261106)
out = []

def emit(*f):
    out.append(" ".join(str(x) for x in f))

def bufbits(bv, garbage=False):
    if garbage:
        return rng.randrange(65536)
    return rng.randrange(1 << bv) if bv > 0 else 0

# ---------------------------------------------------------------- bi_reverse
for ln in range(1, 16):
    for code in [0, 1, 2, 3, 5, (1 << ln) - 1, 1 << (ln - 1), rng.randrange(1 << ln), rng.randrange(1 << ln),
                 0xffffffff, 0x80000000, rng.randrange(1 << 32)]:
        emit("bi_reverse", code, ln)
for ln in [0, -1, -5, 16, 17, 20, 31, 32, 33, 40]:
    for code in [0, 1, 0xffffffff, 0x80000001, rng.randrange(1 << 32)]:
        emit("bi_reverse", code, ln)

# ---------------------------------------------------------------- sendbits
for bv in range(0, 17):
    for ln in range(1, 17):
        vals = {0, (1 << ln) - 1, rng.randrange(1 << ln)}
        if ln == 16:
            vals = {0, 1, (1 << 15) - 1, rng.randrange(1 << 15)}   # value << bi_valid must fit an int
        for v in sorted(vals):
            if ln == 16 and bv > 15 and v >= (1 << 15):
                continue
            emit("sendbits", bufbits(bv), bv, rng.choice([0, 1, 5]), f"{v}:{ln}")
for _ in range(250):
    bv = rng.randrange(0, 17)
    n = rng.randrange(1, 13)
    pairs = []
    for _ in range(n):
        ln = rng.randrange(1, 16)
        pairs.append(f"{rng.randrange(1 << ln)}:{ln}")
    emit("sendbits", bufbits(bv, garbage=rng.random() < 0.25), bv, rng.choice([0, 0, 1, 2, 7]), ",".join(pairs))
emit("sendbits", 0, 0, 0, "-")
emit("sendbits", 65535, 16, 3, "-")

# ---------------------------------------------------------------- bit buffer operations
for name in ["windup", "flush", "flushbits"]:
    for bv in range(-3, 21):
        for _ in range(3):
            emit("bitop", name, bufbits(max(bv, 0), garbage=rng.random() < 0.3), bv, rng.choice([0, 1, 5]))
for bv in range(0, 17):
    for _ in range(4):
        emit("bitop", "align", bufbits(bv), bv, rng.choice([0, 1, 5]))

# ---------------------------------------------------------------- stored blocks
for ln in [0, 1, 2, 3, 4, 5, 255, 256, 1000, 65534, 65535, 65536, 65537, 70000]:
    for last in [0, 1]:
        bv = rng.randrange(0, 17)
        emit("stored", bufbits(bv), bv, rng.choice([0, 3]), last, "ramp", ln)
emit("stored", 5, 3, 0, 1, "null", 0)
emit("stored", 0, 0, 0, 0, "null", 0)
emit("stored", 255, 8, 2, 0, "ramp", 0)
for bv in range(0, 17):
    emit("stored", bufbits(bv), bv, 0, rng.randrange(2), "ramp", rng.randrange(0, 40))

# ---------------------------------------------------------------- detect_data_type
BLOCK = list(range(0, 7)) + list(range(14, 26)) + list(range(28, 32))
for i in range(256):
    emit("detect", f"{i}:1")
    emit("detect", f"{i}:65535")
emit("detect", "-")
emit("detect", "256:5")
for _ in range(120):
    k = rng.randrange(1, 6)
    emit("detect", ",".join(f"{rng.choice([rng.randrange(256), rng.randrange(7, 14), rng.randrange(32, 256), rng.choice(BLOCK)])}:{rng.randrange(1, 4)}" for _ in range(k)))
emit("detect", "7:1,8:1,11:1,12:1,26:1,27:1")
emit("detect", "7:1,8:1,11:1,12:1,26:1,27:1,9:1")
emit("detect", "7:1,8:1,11:1,12:1,26:1,27:1,31:1")
emit("detect", "7:1,32:1")
emit("detect", "14:1,10:1")
emit("detect", "13:1")
emit("detect", "10:1,31:1")
emit("detect", "5:1,6:1,7:1")

# ---------------------------------------------------------------- gen_codes
def optimal_counts(lens):
    c = [0] * 16
    for l in lens:
        if l:
            c[l] += 1
    return c
for _ in range(60):
    n = rng.randrange(1, 288)
    # a complete-ish length set from a random Kraft-like process, lengths 1..15
    lens = [rng.choice([0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]) for _ in range(n)]
    mc = rng.choice([n - 1, n - 1, n - 2, min(287, n + 3)]) if n > 1 else 0
    bc = optimal_counts(lens)
    spec = ",".join(f"{i}:{l}" for i, l in enumerate(lens) if l) or "-"
    emit("gen_codes", mc, ",".join(map(str, bc)), spec)
for _ in range(40):   # bl_count[0] is not zero here (gen_codes does not require it)
    n = rng.randrange(2, 40)
    lens = [rng.randrange(0, 16) for _ in range(n)]
    bc = [rng.randrange(0, 70000 if rng.random() < 0.2 else 8) % 65536 for _ in range(16)]
    emit("gen_codes", n - 1, ",".join(map(str, bc)), ",".join(f"{i}:{l}" for i, l in enumerate(lens) if l) or "-")
# the static literal tree lengths: 0..143 -> 8, 144..255 -> 9, 256..279 -> 7, 280..287 -> 8
emit("gen_codes", 287, "0,0,0,0,0,0,0,24,152,112,0,0,0,0,0,0", "0-143:8,144-255:9,256-279:7,280-287:8")
emit("gen_codes", 29, "0,0,0,0,0,30,0,0,0,0,0,0,0,0,0,0", "0-29:5")
emit("gen_codes", -1, "0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0", "0-5:3")
emit("gen_codes", 0, "65535,65535,0,0,0,0,0,0,0,0,0,0,0,0,0,7", "0:1")
emit("gen_codes", 3, "1,65535,3,65535,5,6,7,8,9,10,11,12,13,14,15,16", "0:1,1:15,2:2,3:15")

# ---------------------------------------------------------------- build_tree
def fib(k):
    a, b = [1, 1]
    r = []
    for _ in range(k):
        r.append(a)
        a, b = b, a + b
    return r

def freqspec(d):
    return ",".join(f"{i}:{v}" for i, v in sorted(d.items())) or "-"

ELEMS = {"l": 286, "d": 30, "bl": 19}
for which, ne in ELEMS.items():
    emit("buildtree", which, 0, 0, "-")
    for i in [0, 1, 2, ne - 1, ne // 2]:
        emit("buildtree", which, 100, 100, f"{i}:1")
        emit("buildtree", which, 100, 100, f"{i}:7")
    emit("buildtree", which, 0, 0, f"0:1,1:1")
    emit("buildtree", which, 5, 5, f"{ne-2}:3,{ne-1}:3")
    emit("buildtree", which, 5, 5, f"0:65535,{ne-1}:65535")
    emit("buildtree", which, 2 ** 64 - 1, 2 ** 64 - 1, f"1:1")
    emit("buildtree", which, 0, 0, f"0-{ne-1}:1")
    emit("buildtree", which, 0, 0, f"0-{ne-1}:65535")
    for _ in range(40):
        k = rng.randrange(1, ne + 1)
        idx = rng.sample(range(ne), k)
        emit("buildtree", which, rng.randrange(1000), rng.randrange(1000),
             freqspec({i: rng.choice([1, 2, 3, rng.randrange(1, 100), rng.randrange(1, 65536)]) for i in idx}))
    # skewed (geometric) and Fibonacci frequencies force the bit length limit repair
    for k in range(3, ne + 1):
        if k > 24 and k != ne:
            continue
        f = fib(min(k, 24))
        idx = rng.sample(range(ne), min(k, 24)) if rng.random() < 0.5 else list(range(min(k, 24)))
        emit("buildtree", which, 0, 0, freqspec({i: f[j] for j, i in enumerate(idx)}))
        emit("buildtree", which, 0, 0, freqspec({i: f[j] for j, i in enumerate(reversed(idx))}))
    # chain-shaped trees (every merge joins a leaf and the previous node): 1,2,3,5,8,... up to 65535
    f2 = fib(26)[1:]
    for k in range(4, min(ne, 24) + 1):
        pre = ",256:0" if which == "l" else ""
        base = list(range(k)) if which != "l" else [i for i in range(k + 1) if i != 256]
        emit("buildtree", which, 0, 0, freqspec({i: f2[j] for j, i in enumerate(base[:k])}) + pre)
        emit("buildtree", which, 9, 9, freqspec({i: f2[k - 1 - j] for j, i in enumerate(base[:k])}) + pre)
    g = {i: 2 ** (i % 15) for i in range(ne)}
    emit("buildtree", which, 0, 0, freqspec(g))
    emit("buildtree", which, 0, 0, freqspec({i: 3 ** (i % 10) for i in range(ne)}))
    emit("buildtree", which, 0, 0, freqspec({i: 1 + (i * i) % 1000 for i in range(ne)}))

# ---------------------------------------------------------------- scan_tree / send_tree / build_bl_tree / send_all_trees
def lens_for(n, kind):
    if kind == "uniform":
        return [rng.randrange(0, 16)] * n
    if kind == "runs":
        r = []
        while len(r) < n:
            r += [rng.choice([0, 0, 0, 1, 5, 8, 9, 15])] * rng.choice([1, 2, 3, 4, 5, 6, 7, 8, 10, 11, 12, 20, 138, 139, 150])
        return r[:n]
    if kind == "zeros":
        return [0] * n
    return [rng.choice([0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]) for _ in range(n)]

def runspec(lens):
    return ",".join(f"{i}:{l}" for i, l in enumerate(lens) if l) or "-"

for _ in range(160):
    lmax = rng.choice([256, 256, 257, 270, 285, rng.randrange(256, 286)])
    dmax = rng.choice([0, 1, 5, 29, rng.randrange(0, 30)])
    kind = rng.choice(["uniform", "runs", "zeros", "random", "runs", "runs"])
    ll = lens_for(lmax + 1, kind)
    dl = lens_for(dmax + 1, rng.choice(["uniform", "runs", "zeros", "random"]))
    if rng.random() < 0.1:
        ll[rng.randrange(len(ll))] = rng.choice([16, 17, 18, 19, 20])
    bv = rng.randrange(0, 17)
    emit("trees", lmax, runspec(ll), dmax, runspec(dl), bufbits(bv), bv, rng.choice([0, 0, 1, 3]))
# exact repeat-count boundaries: a run of length r of the value v inside an otherwise-zero tree
for v in [0, 1, 7]:
    for r in list(range(1, 16)) + [136, 137, 138, 139, 140, 150, 276]:
        ll = [0] * 286
        for i in range(10, min(10 + r, 286)):
            ll[i] = v
        emit("trees", 285, runspec(ll), 5, runspec([3, 3, 3, 3, 3, 3]), 0, 0, 0)
        ll2 = [4] * 3 + [v] * r + [9]
        ll2 = (ll2 + [0] * 300)[:257]
        emit("trees", 256, runspec(ll2), 0, "-", 0, 0, 0)
emit("trees", 256, "-", 0, "-", 0, 0, 0)

# ---------------------------------------------------------------- symbol sets for blocks and tallies
def lit(c, n=1):
    return f"l{c}" + (f"*{n}" if n != 1 else "")

def mat(d, l, n=1):
    return f"m{d}:{l}" + (f"*{n}" if n != 1 else "")

TEXT = [32] * 8 + list(range(97, 123)) * 2 + [101, 116, 97, 111, 105, 110, 10, 46, 44]

def rand_syms(kind, n):
    s = []
    for _ in range(n):
        r = rng.random()
        if kind == "text":
            if r < 0.7:
                s.append(lit(rng.choice(TEXT)))
            else:
                s.append(mat(rng.choice([1, 2, 3, 5, 8, 20, 100, 300, rng.randrange(1, 32769)]), rng.choice([0, 1, 2, 5, 20, 255, rng.randrange(256)])))
        elif kind == "binary":
            s.append(lit(rng.randrange(256)))
        elif kind == "matches":
            s.append(mat(rng.randrange(1, 32769), rng.randrange(256)))
        elif kind == "ctrl":
            s.append(lit(rng.choice(BLOCK + TEXT)))
        elif kind == "mixed":
            if r < 0.5:
                s.append(lit(rng.randrange(256)))
            else:
                s.append(mat(rng.choice([1, 2, 4, 8, 16, 32768, rng.randrange(1, 32769)]), rng.randrange(256)))
        elif kind == "few":
            s.append(lit(rng.choice([65, 66])))
    return s

def total_bytes(syms):
    t = 0
    for x in syms:
        n = 1
        if "*" in x:
            x, n = x.split("*")
            n = int(n)
        t += n if x[0] == "l" else n * (int(x.split(":")[1]) + 3)
    return t

# ---------------------------------------------------------------- tally
for lit_size in [2, 3, 4, 5, 8, 17, 40]:
    for n in sorted({0, 1, lit_size - 2, lit_size - 1}):
        if n < 0 or n > lit_size - 1:
            continue
        syms = rand_syms("mixed", n)
        emit("tally", lit_size, ",".join(syms) or "-")
for lit_size in [2, 3, 5, 9]:   # the buffer is allowed to fill past sym_end: the result is (sym_next == sym_end)
    for n in [lit_size, lit_size + 1]:
        emit("tally", lit_size, ",".join(rand_syms("mixed", n)))
emit("tally", 16, "l300,l256,l257,l0,l255,m1:0,m32768:255,m32768:0,m1:255,m256:7,m257:7,m4096:3")
emit("tally", 16, "m128:0*3,m129:0*3,l1*5")
emit("tally", 300, "m1:0*50,m2:0*50,m3:0*50,m4:0*50,m5:0*50,l9*40")
for d in [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 16, 17, 32, 33, 64, 65, 128, 129, 256, 257, 258, 384, 385, 512, 513, 1024, 1025, 2048, 4096, 8192, 16384, 24576, 24577, 32767, 32768]:
    emit("tally", 4, f"m{d}:3")
for lc in list(range(0, 12)) + [30, 31, 32, 62, 63, 64, 126, 127, 128, 253, 254, 255]:
    emit("tally", 4, f"m100:{lc}")

# ---------------------------------------------------------------- blocks
def block(level, strategy, dt, bv, syms, stored_len, last, buf="ramp", lit_size=None):
    n = sum(int(x.split("*")[1]) if "*" in x else 1 for x in syms)
    if level == 0:
        stored_len = min(stored_len, 900)   # level 0 forces a stored block: it must fit the pending buffer
    if lit_size is None:
        lit_size = max(n + 2, 16)
    emit("block", level, strategy, dt, bufbits(bv), bv, lit_size, stored_len, buf, last, ",".join(syms) or "-")

# empty and tiny blocks
for level in [0, 1, 6]:
    for last in [0, 1]:
        for buf in ["ramp", "null"]:
            block(level, 0, 2, 0, [], 0, last, buf)
            block(level, 0, 0, 3, [lit(65)], 1, last, buf)
            block(level, 0, 1, 5, [lit(65), lit(66)], 2, last, buf)
            block(level, 4, 2, 16, [lit(0)], 1, last, buf)
for dt in [0, 1, 2]:
    block(6, 0, dt, 0, [lit(0)], 1, 0)
    block(6, 0, dt, 0, [lit(10)], 1, 0)
    block(6, 0, dt, 0, [lit(200)], 1, 0)
    block(6, 0, dt, 0, [], 0, 0)
    block(6, 0, dt, 0, [lit(7), lit(8)], 2, 0)
# sweep of stored_len across the stored/static/dynamic decision boundaries for some fixed sets
for kind, n in [("text", 30), ("binary", 24), ("mixed", 40), ("matches", 10), ("few", 12), ("text", 150)]:
    syms = rand_syms(kind, n)
    tb = total_bytes(syms)
    for sl in sorted(set(list(range(0, 40)) + [tb - 2, tb - 1, tb, tb + 1, tb + 2, 2 * tb, 70000])):
        if sl < 0:
            continue
        block(rng.choice([1, 6, 9]), rng.choice([0, 0, 1, 2, 3]), rng.choice([0, 1, 2]), rng.randrange(0, 17), syms, sl, rng.randrange(2))
# random blocks
for _ in range(220):
    kind = rng.choice(["text", "binary", "matches", "ctrl", "mixed", "few", "text", "mixed"])
    n = rng.choice([1, 2, 3, 5, 10, 25, 60, 120, 250, 400])
    syms = rand_syms(kind, n)
    tb = total_bytes(syms)
    sl = rng.choice([tb, tb, tb, max(0, tb - rng.randrange(0, 20)), tb + rng.randrange(0, 20)])
    level = rng.choice([0, 1, 4, 6, 9, 9])
    strategy = rng.choice([0, 0, 0, 1, 2, 3, 4])
    bv = rng.randrange(0, 17)
    block(level, strategy, rng.choice([0, 1, 2, 2]), bv, syms, sl, rng.randrange(2), rng.choice(["ramp", "ramp", "ramp", "null"]))
# many small blocks: the stored/static/dynamic decisions at their boundaries (rounding of the byte counts,
# static_lenb <= opt_lenb, stored_len + 4 <= opt_lenb)
for _ in range(900):
    kind = rng.choice(["text", "binary", "mixed", "few", "ctrl", "matches"])
    n = rng.randrange(1, 40)
    syms = rand_syms(kind, n)
    tb = total_bytes(syms)
    block(rng.choice([1, 6, 9]), rng.choice([0, 0, 0, 4]), rng.choice([0, 2]), rng.randrange(0, 17), syms,
          rng.choice([tb, rng.randrange(0, tb + 20), rng.randrange(0, 80)]), rng.randrange(2), "ramp")
for _ in range(6):
    syms = rand_syms("text", rng.randrange(5, 30))
    for sl in range(0, 80):
        block(6, 0, 2, 0, syms, sl, 0, "ramp")
# many equal-frequency symbols (dynamic trees of nearly-uniform depth)
for k in [2, 3, 4, 7, 8, 9, 15, 16, 17, 31, 32, 33, 100, 200, 256]:
    syms = [lit(c, 3) for c in range(k)]
    block(6, 0, 2, 0, syms, 3 * k, 1)
    syms = [lit(c, 1 + (c % 5)) for c in range(k)]
    block(6, 0, 2, 4, syms, 3 * k, 0)
# bit length limit: Fibonacci frequencies over literals (needs > 15 levels) and over distance codes
f = fib(17)
syms = [lit(65 + i, f[i]) for i in range(17)]
block(9, 0, 2, 0, syms, sum(f), 1, lit_size=sum(f) + 2)
f = fib(16)
syms = [lit(65 + i, f[i]) for i in range(16)]
block(9, 0, 2, 7, syms, sum(f), 0, lit_size=sum(f) + 2)
f = fib(17)
dd = [1, 2, 3, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193, 257, 385, 513, 769, 1025, 1537, 2049, 3073, 4097, 6145, 8193, 12289, 16385, 24577, 32768]
syms = [mat(dd[i], 5, f[i]) for i in range(17)]
block(9, 0, 2, 0, syms, 100000, 1, lit_size=sum(f) + 2)
syms = [mat(dd[i], i, f[i]) for i in range(17)] + [lit(3, 1)]
block(9, 0, 1, 1, syms, 50, 0, lit_size=sum(f) + 3)

print("\n".join(out))
print("init")
print("tables")
