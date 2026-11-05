#!/usr/bin/env python3
"""Inputs for the deflate.c / compress.c differential test, written to stdout. Deterministic (fixed seed).

Case lines (the grammar is implemented by tests/c/deflate.c and tests/lean/Driver/Deflate.lean):
  session TOKEN...         one stream, driven by the tokens in order; the output is the tokens' results and the
                           compressed bytes written to the output buffer
  compress2 LEVEL DESTCAP xSRCHEX | compress DESTCAP... (same with LEVEL ignored) | compress2_z | compress_z
  bound N                  compressBound, compressBound_z
Tokens:
  I:level:method:wbits:mem:strat[:v|:s]  deflateInit2_ (v = wrong version, s = wrong stream_size)    I1:level  deflateInit_
  IN:hex      the input buffer (before the first D)          D:flush:inbytes:outbytes   feed more input, call deflate
  P:level:strategy deflateParams       S:hex deflateSetDictionary   G deflateGetDictionary   R deflateReset
  K:bits:value deflatePrime            C deflateCopy (continue with the copy)               B deflateBound (of the input)
  T:good:lazy:nice:chain deflateTune   Q deflatePending   U deflateUsed
  H:text:time:os:hcrc:extra:name:comment  deflateSetHeader (hex or -)                      E deflateEnd
Undefined behaviour of the C is never generated.
"""
import random

rng = random.Random(20261106)
out = []

def emit(*f):
    out.append(" ".join(str(x) for x in f))

WORDS = [b"the", b"quick", b"brown", b"fox", b"jumps", b"over", b"lazy", b"dog", b"zlib", b"deflate", b"window", b"huffman"]

def data(kind, n):
    if kind == "rand":
        return bytes(rng.randrange(256) for _ in range(n))
    if kind == "zero":
        return bytes(n)
    if kind == "text":
        b = b""
        while len(b) < n:
            b += rng.choice(WORDS) + b" "
        return b[:n]
    if kind == "period":
        p = bytes(rng.randrange(256) for _ in range(7))
        return (p * (n // 7 + 1))[:n]
    if kind == "ramp":
        return bytes(i & 255 for i in range(n))
    if kind == "runs":
        b = b""
        while len(b) < n:
            b += bytes([rng.randrange(4)]) * rng.randrange(1, 40)
        return b[:n]
    if kind == "mixed":
        b = b""
        while len(b) < n:
            if rng.random() < 0.5:
                b += rng.choice(WORDS) + b" "
            else:
                b += bytes(rng.randrange(256) for _ in range(rng.randrange(1, 12)))
        return b[:n]
    raise ValueError(kind)

KINDS = ["rand", "zero", "text", "period", "ramp", "runs", "mixed"]

def hx(b):
    return b.hex()

def sess(*toks):
    emit("session", *toks)

# ---------------------------------------------------------------- deflateInit2_ parameter sweep
for level in [-2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]:
    sess(f"I:{level}:8:15:8:0")
for method in [0, 7, 8, 9, -1]:
    sess(f"I:6:{method}:15:8:0")
for wb in [-16, -15, -14, -9, -8, -1, 0, 7, 8, 9, 10, 15, 16, 17, 24, 25, 31, 32, 40]:
    sess(f"I:6:8:{wb}:8:0")
for mem in [-1, 0, 1, 2, 8, 9, 10, 100]:
    sess(f"I:6:8:15:{mem}:0")
for st in [-1, 0, 1, 2, 3, 4, 5, 6]:
    sess(f"I:6:8:15:8:{st}")
sess("I:6:8:15:8:0:v")
sess("I:6:8:15:8:0:s")
sess("I1:6")
sess("I1:-1")
sess("I1:10")
# the 8-bit window: windowBits 8 is allowed for raw/zlib-less? (only wrap == 1) and changed to 9
sess("I:6:8:8:8:0", "IN:" + hx(b"abc"), "D:4:3:100")
sess("I:6:8:-8:8:0", "IN:" + hx(b"abc"), "D:4:3:100")
sess("I:6:8:24:8:0", "IN:" + hx(b"abc"), "D:4:3:100")

# ---------------------------------------------------------------- deflate: all flush modes, strategies
SIZES = [0, 1, 2, 3, 4, 5, 10, 33, 100, 258, 300, 700]
for level in [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, -1]:
    for strat in range(5):
        for wb in [15, -15, 31]:
            kind = KINDS[rng.randrange(len(KINDS))]
            n = rng.choice(SIZES)
            d = data(kind, n)
            sess(f"I:{level}:8:{wb}:8:{strat}", "IN:" + hx(d), f"D:4:{n}:{n + 200}")

for kind in KINDS:
    for n in rng.sample([0, 1, 3, 100, 600], 3):
        d = data(kind, n)
        for flush in range(0, 6):
            for level in [0, 1, 6, 9]:
                sess(f"I:{level}:8:15:8:0", "IN:" + hx(d), f"D:{flush}:{n}:{n + 300}", "D:4:0:300")

# small windows and symbol buffers: block flushes, window slides, hash slides
# (each block flush costs seconds in the Lean runtime because of the depth of its heap tables, so few sessions)
_small = [(level, strat, wm, kind) for level in [0, 1, 3, 4, 6, 9] for strat in [0, 1, 2, 3, 4]
          for wm in [(9, 1)] for kind in ["text", "mixed", "runs", "rand", "period"]]
for (level, strat, (wb, mem), kind) in rng.sample(_small, 12):
    n = 800
    d = data(kind, n)
    # fed in pieces of 100 bytes
    sess(f"I:{level}:8:{wb}:{mem}:{strat}", "IN:" + hx(d), *([f"D:0:100:{n + 2000}"] * (n // 100 + 1)), "D:4:0:3000")

# chunked input and output
for level in [0, 1, 6, 9]:
    for strat in [0, 1, 2, 3, 4]:
        for (ic, oc) in [(1, 1), (7, 5), (50, 13), (3, 1000), (200, 3)]:
            kind = rng.choice(KINDS)
            n = rng.choice([60, 200, 400])
            d = data(kind, n)
            toks = [f"I:{level}:8:15:8:{strat}", "IN:" + hx(d)]
            k = (n // ic) + 1
            if ic == 1 or oc == 1:
                k = min(k, 400)
            for _ in range(min(k, 80)):
                toks.append(f"D:0:{ic}:{oc}")
            for _ in range(12):
                toks.append(f"D:4:{ic}:{oc}")
            for _ in range(600 if oc <= 5 else 0):
                break
            sess(*toks)

# mid-stream flushes with chunked output
for level in [1, 6, 9, 0]:
    for flush in [1, 2, 3, 5]:
        d = data("mixed", 900)
        toks = [f"I:{level}:8:15:8:0", "IN:" + hx(d)]
        for i in range(6):
            toks.append(f"D:{flush}:150:40")
        toks += ["D:4:0:2000"]
        sess(*toks)

# repeated calls after finish, bad calls
d = data("text", 100)
sess("I:6:8:15:8:0", "IN:" + hx(d), "D:4:100:500", "D:4:0:500", "D:0:0:500", "D:0:0:0", "D:9:0:10", "D:-1:0:10", "R", "D:4:100:500")
sess("I:6:8:15:8:0", "IN:" + hx(d), "D:0:0:0", "D:0:100:0", "D:4:0:500")
sess("I:6:8:15:8:0", "IN:" + hx(d), "D:0:50:500", "D:0:0:500", "D:4:0:500")

# ---------------------------------------------------------------- deflateParams
for l1 in [0, 1, 4, 6, 9]:
    for l2 in [0, 1, 3, 6, 9, -1, 10, -2]:
        for s1, s2 in [(0, 0), (0, 1), (0, 2), (1, 3), (3, 4), (0, 6)]:
            d = data(rng.choice(KINDS), 400)
            sess(f"I:{l1}:8:15:8:{s1}", "IN:" + hx(d), "D:0:150:1000", f"P:{l2}:{s2}", "D:0:150:1000", "D:4:100:1000")
# params with no pending data / before first deflate / with small output
for l1 in [0, 6]:
    for l2 in [0, 6, 9]:
        d = data("text", 300)
        sess(f"I:{l1}:8:15:8:0", "IN:" + hx(d), f"P:{l2}:0", "D:0:100:50", f"P:{(l2 + 1) % 10}:2", "D:0:100:2", "D:4:100:2000")
# level-0 history kept and later slid / cleared
d = data("text", 1800)
for l2 in [1, 6, 9]:
    sess("I:0:8:9:1:0", "IN:" + hx(d), "D:0:500:600", "D:0:500:600", f"P:{l2}:0", "D:0:400:600", "D:4:400:3000")
    sess("I:0:8:9:1:0", "IN:" + hx(d), "D:0:900:1200", "D:0:900:1200", f"P:{l2}:0", "D:4:0:3000")

# ---------------------------------------------------------------- deflateSetDictionary / deflateGetDictionary
for wb in [15, -15, 31, 9]:
    for dl in [0, 1, 2, 3, 100, 511, 512, 513, 1000, 3000]:
        for level in [1, 6, 9]:
            dic = data("text", dl)
            msg = data("text", 200)
            sess(f"I:{level}:8:{wb}:8:0", "S:" + hx(dic), "IN:" + hx(msg), "D:4:200:500", "G")
for wb in [15, -15, 31]:
    d = data("mixed", 300)
    sess(f"I:6:8:{wb}:8:0", "IN:" + hx(d), "D:0:100:400", "S:" + hx(b"abcabc"), "D:4:200:400")
    sess(f"I:6:8:{wb}:8:0", "IN:" + hx(d), "D:0:100:400", "G", "D:4:200:400", "G")
    sess(f"I:6:8:{wb}:8:0", "G", "IN:" + hx(d), "D:0:300:1000", "G", "S:" + hx(b"zz"))
sess("I:6:8:15:8:0", "S:", "IN:" + hx(b"hello"), "D:4:5:100")
sess("E", "G")
# dictionary then reset then more
sess("I:6:8:15:8:0", "S:" + hx(data("text", 50)), "IN:" + hx(data("text", 50)), "D:4:50:200", "R", "S:" + hx(data("text", 20)), "D:4:0:200")

# ---------------------------------------------------------------- deflatePrime, deflateTune, deflatePending/Used, deflateBound, Reset
for bits in [-1, 0, 1, 7, 8, 9, 15, 16, 17]:
    for value in [0, 1, 5, 0xff, 0x1234, -1, -2]:
        sess("I:6:8:-15:8:0", f"K:{bits}:{value}", "IN:" + hx(b"abcdefabcdef"), "D:4:12:100")
sess("I:6:8:-15:8:0", "K:3:5", "K:7:99", "K:16:0xabcd".replace("0xabcd", "43981"), "IN:" + hx(b"xyz"), "D:2:3:20", "K:5:7", "D:4:0:100")
sess("I:6:8:-15:8:0", "IN:" + hx(data("text", 200)), "D:0:100:3", "K:9:300", "D:0:0:3", "D:4:0:500")
for g, l, n, c in [(0, 0, 0, 0), (4, 4, 8, 4), (8, 16, 32, 32), (32, 258, 258, 4096), (1, 3, 3, 1), (-1, -1, -1, -1), (100, 1000, 1000, 1000)]:
    for level in [4, 9]:
        sess(f"I:{level}:8:15:8:0", f"T:{g}:{l}:{n}:{c}", "IN:" + hx(data("text", 400)), "D:4:400:600", "Q", "U")
sess("I:6:8:15:8:0", "Q", "U", "IN:" + hx(data("text", 100)), "D:0:100:1", "Q", "U", "D:4:0:1000", "Q", "U")
sess("I:6:8:15:8:0", "IN:" + hx(data("text", 100)), "D:5:100:1000", "Q", "U")
for wb in [15, -15, 31, 9]:
    for mem in [1, 8, 9]:
        for level in [0, 1, 6, 9]:
            sess(f"I:{level}:8:{wb}:{mem}:0", "IN:" + hx(data("text", 1000)), "B")
sess("I:6:8:31:8:0", "H:1:5:3:1:0102:6e616d65:636f6d6d656e74", "IN:" + hx(b"hello hello hello"), "B", "D:4:17:100")
# stream reset: reuse
sess("I:6:8:15:8:0", "IN:" + hx(data("text", 100)), "D:4:100:500", "R", "D:4:100:500", "R", "D:2:50:500", "R")
for n in [0, 1, 11, 12, 13, 100, 4095, 4096, 4097, 16383, 16384, 1 << 20, (1 << 25), (1 << 25) + 1, (1 << 32) - 1, 1 << 32, (1 << 64) - 1]:
    emit("bound", n)

# ---------------------------------------------------------------- gzip headers
HDRS = [
    "H:0:0:3:0:-:-:-",
    "H:1:12345:255:0:-:-:-",
    "H:0:0:0:1:-:-:-",
    "H:1:4294967295:7:1:aabbcc:6e616d65:636f6d6d:".rstrip(":"),
    "H:0:1:3:0:-:6e:-",
    "H:0:1:3:0:-:-:63",
    "H:0:1:3:1:01:-:-",
    "H:0:0:3:1:-:6162:6364",
    "H:0:0:3:0:" + "ab" * 300 + ":" + "61" * 200 + ":" + "62" * 150,
    "H:0:0:3:1:" + "cd" * 70 + ":" + "61" * 40 + ":" + "62" * 30,
]
HDRS = [h if h.count(":") == 7 else h for h in HDRS]
for h in HDRS:
    for (oc) in [1000, 7, 1, 25, 3]:
        d = data("text", 120)
        toks = ["I:6:8:31:8:0", h, "IN:" + hx(d)]
        if oc >= 1000:
            toks += ["D:4:120:2000"]
        else:
            toks += [f"D:0:60:{oc}"] * 150 + [f"D:4:60:{oc}"] * 500
        sess(*toks)
# header set at a bad time / on non-gzip stream
sess("I:6:8:15:8:0", "H:0:0:3:0:-:-:-", "IN:" + hx(b"abc"), "D:4:3:100")
sess("I:6:8:31:8:0", "IN:" + hx(b"abc"), "D:0:3:100", "H:0:0:3:0:-:-:-", "D:4:0:100")
sess("I:6:8:31:8:0", "H:0:0:3:0:-:-:-", "H:1:1:1:1:-:-:-", "IN:" + hx(b"abc"), "D:4:3:100")

# ---------------------------------------------------------------- deflateCopy
for level in [0, 1, 6, 9]:
    for strat in [0, 1, 2, 3]:
        for wb in [15, -15, 31, 9]:
            d = data("mixed", 600)
            sess(f"I:{level}:8:{wb}:{rng.choice([1, 8])}:{strat}", "IN:" + hx(d), "D:0:300:50", "C", "D:0:100:1000", "D:4:200:1000")
            sess(f"I:{level}:8:{wb}:8:{strat}", "IN:" + hx(d), "D:0:600:40", "C", "D:4:0:1000")
sess("I:6:8:15:8:0", "C", "IN:" + hx(b"a"), "D:4:1:100")
sess("E", "C")
d = data("text", 2500)
sess("I:6:8:9:1:0", "IN:" + hx(d), "D:0:1500:100", "C", "D:4:1000:3000")
sess("I:0:8:9:1:0", "IN:" + hx(d), "D:0:1500:100", "C", "D:4:1000:3000")

# ---------------------------------------------------------------- deflateEnd (status of the result)
sess("I:6:8:15:8:0", "E")
sess("I:6:8:15:8:0", "IN:" + hx(b"abc"), "D:0:3:100", "E")
sess("I:6:8:15:8:0", "IN:" + hx(b"abc"), "D:4:3:100", "E", "E")

# ---------------------------------------------------------------- compress / compress2
for level in [-1, 0, 1, 6, 9, 10, -2]:
    for kind in ["text", "rand", "zero", "mixed"]:
        for n in [0, 1, 10, 100, 250]:
            d = data(kind, n)
            emit("compress2", level, n + 64, "x" + hx(d))
            emit("compress2_z", level, n + 64, "x" + hx(d))
for n in [0, 10, 100]:
    d = data("text", n)
    for dc in [0, 1, 2, 5, 6, 7, 11, 12, n // 2, n, n + 6, n + 20]:
        emit("compress", 0, dc, "x" + hx(d))
        emit("compress_z", 0, dc, "x" + hx(d))
        emit("compress2", 6, dc, "x" + hx(d))
for n in [0, 1, 100, 4095, 4096, 1 << 20, (1 << 25) + 3, (1 << 32), (1 << 40) + 5, (1 << 64) - 1]:
    emit("bound", n)

print("\n".join(out))
