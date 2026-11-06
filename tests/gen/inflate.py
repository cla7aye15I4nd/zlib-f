#!/usr/bin/env python3
"""Inputs for the inflate.c differential test, written to stdout.

Deterministic: fixed seed, no clock, no environment. One line per case (format: tests/c/inflate.c):
  inflate WB INCH OUTCH FLUSH OPTS hex:DICT hex:INPUT
The inputs are deflate, zlib and gzip streams made with Python's zlib module (and by hand for gzip headers with
extra, name, comment and header CRC), then corrupted, truncated, chunked and fed with every flush value.
"""
import random
import struct
import zlib

rng = random.Random(20261105)
out = []

Z_NO_FLUSH, Z_SYNC_FLUSH, Z_FINISH, Z_BLOCK, Z_TREES = 0, 2, 4, 5, 6
OPT_HEAD, OPT_COPY, OPT_GETDICT, OPT_PRIME, OPT_SETDICT, OPT_NOCHECK, OPT_SYNC = 1, 2, 4, 8, 16, 32, 64

def case(wb, inch, outch, flush, opts, dic, data):
    out.append("inflate %d %d %d %d %d hex:%s hex:%s" % (wb, inch, outch, flush, opts, bytes(dic).hex(), bytes(data).hex()))

# ---- data ----------------------------------------------------------------------------------------------------------
WORDS = [b"the ", b"quick ", b"brown ", b"fox ", b"jumps ", b"over ", b"lazy ", b"dog ", b"zlib ", b"inflate ", b"\n"]

def text(n):
    b = bytearray()
    while len(b) < n:
        b += rng.choice(WORDS)
    return bytes(b[:n])

def randbytes(n):
    return bytes(rng.randrange(256) for _ in range(n))

def ramp(n):
    return bytes((i * 7 + 3) & 255 for i in range(n))

def longrange(n):
    blk = randbytes(300)
    gap = randbytes(900)
    return (blk + gap + blk + gap[:100] + blk)[:n]

KINDS = {"text": text, "rand": randbytes, "zero": lambda n: bytes(n), "ramp": ramp, "long": longrange}

# ---- streams -------------------------------------------------------------------------------------------------------
def deflate(data, level=6, wbits=15, strategy=0, mem=8, zdict=None):
    kw = {}
    if zdict is not None:
        kw["zdict"] = zdict
    c = zlib.compressobj(level, zlib.DEFLATED, wbits, mem, strategy, **kw)
    return c.compress(data) + c.flush()

def gzip_manual(data, flags=0, extra=b"", name=b"", comment=b"", mtime=0x12345678, xfl=2, os_=3, bad_hcrc=False,
                level=6):
    hdr = bytes([0x1f, 0x8b, 8, flags]) + struct.pack("<I", mtime) + bytes([xfl, os_])
    if flags & 4:
        hdr += struct.pack("<H", len(extra)) + extra
    if flags & 8:
        hdr += name + b"\0"
    if flags & 16:
        hdr += comment + b"\0"
    if flags & 2:
        h = zlib.crc32(hdr) & 0xffff
        if bad_hcrc:
            h ^= 1
        hdr += struct.pack("<H", h)
    body = deflate(data, level, -15)
    return hdr + body + struct.pack("<II", zlib.crc32(data) & 0xffffffff, len(data) & 0xffffffff)

def corrupt(stream, how):
    s = bytearray(stream)
    n = len(s)
    if n == 0:
        return bytes(s)
    if how == "trunc1":
        return bytes(s[:max(n - 1, 0)])
    if how == "trunc4":
        return bytes(s[:max(n - 4, 0)])
    if how == "trunchalf":
        return bytes(s[:n // 2])
    if how == "append":
        return bytes(s) + b"\x99\x98"
    if how.startswith("flip"):
        i = int(how[4:]) % n
        s[i] ^= 0x01 << (i % 8)
        return bytes(s)
    if how.startswith("set"):
        i, v = how[3:].split("_")
        s[int(i) % n] = int(v)
        return bytes(s)
    raise ValueError(how)

ALL = (0, 65536)

# base streams: (name, wbits-for-inflate, stream, original size)
bases = []
def add(name, wb, stream, size):
    bases.append((name, wb, stream, size))

small = {k: f(200) for k, f in KINDS.items()}
med = {k: f(1800) for k, f in KINDS.items()}
for k in KINDS:
    add("z-" + k + "-s6", 15, deflate(small[k], 6), 200)
for lvl in (0, 1, 9):
    add("z-text-l%d" % lvl, 15, deflate(small["text"], lvl), 200)
for st, nm in ((1, "filtered"), (2, "huff"), (3, "rle"), (4, "fixed")):
    add("z-text-" + nm, 15, deflate(small["text"], 6, 15, st), 200)
    add("z-long-" + nm, 15, deflate(med["long"], 6, 15, st), 1800)
add("z-empty", 15, deflate(b"", 6), 0)
add("z-one", 15, deflate(b"a", 6), 1)
add("raw-text", -15, deflate(small["text"], 6, -15), 200)
add("raw-rand", -15, deflate(small["rand"], 6, -15), 200)
add("raw-empty", -15, deflate(b"", 6, -15), 0)
add("gz-text", 31, deflate(small["text"], 6, 31), 200)
add("gz-auto", 47, deflate(small["text"], 6, 31), 200)
add("z-auto", 47, deflate(small["text"], 6, 15), 200)
add("z-wb0", 0, deflate(small["text"], 6, 15), 200)
mediumbases = []
for k in ("text", "rand", "long", "zero"):
    for lvl in (1, 6, 9):
        mediumbases.append(("zm-%s-l%d" % (k, lvl), 15, deflate(med[k], lvl), 1800))
mediumbases.append(("zm-stored", 15, deflate(med["rand"], 0), 1800))
mediumbases.append(("zm-fixed", 15, deflate(med["text"], 6, 15, 4), 1800))
mediumbases.append(("zm-huff", 15, deflate(med["text"], 6, 15, 2), 1800))
mediumbases.append(("rawm-long", -15, deflate(med["long"], 6, -15), 1800))
mediumbases.append(("gzm-text", 31, deflate(med["text"], 6, 31), 1800))

# ---- 1. every small stream under every chunking and flush ----------------------------------------------------------
CHUNKS_SMALL = [(0, 4096), (1, 1), (1, 4096), (3, 5), (7, 2), (0, 1), (5, 300), (0, 257), (0, 258), (0, 259), (2, 100)]
FLUSHES = [Z_NO_FLUSH, Z_FINISH, Z_BLOCK, Z_TREES, Z_SYNC_FLUSH]
for name, wb, stream, size in bases:
    for (ic, oc) in CHUNKS_SMALL:
        case(wb, ic, oc, Z_NO_FLUSH, 0, b"", stream)
    for fl in FLUSHES[1:]:
        for (ic, oc) in ((0, 4096), (1, 3), (4, 1), (0, 64)):
            case(wb, ic, oc, fl, 0, b"", stream)

# ---- 2. medium streams: larger chunks (inflate_fast, window copies) ------------------------------------------------
for name, wb, stream, size in mediumbases:
    for (ic, oc) in ((0, 4096), (0, 300), (0, 1000), (97, 259), (0, 61), (13, 100), (1000, 4096), (0, 258), (0, 517)):
        case(wb, ic, oc, Z_NO_FLUSH, 0, b"", stream)
    case(wb, 0, 4096, Z_FINISH, 0, b"", stream)
    case(wb, 11, 70, Z_BLOCK, 0, b"", stream)
    case(wb, 0, 4096, Z_TREES, 0, b"", stream)

# ---- 3. window sizes: inflate with a smaller window than the stream used ------------------------------------------
dist_stream = deflate(longrange(1800), 9, 15)
for wb in (8, 9, 10, 11, 12, 13, 14, 15, 0):
    case(wb, 0, 4096, Z_NO_FLUSH, 0, b"", dist_stream)
    case(wb, 50, 100, Z_NO_FLUSH, 0, b"", dist_stream)
small_win = deflate(longrange(1800), 9, 9)
for wb in (8, 9, 10, 15, 0):
    case(wb, 0, 4096, Z_NO_FLUSH, 0, b"", small_win)
    case(wb, 33, 100, Z_NO_FLUSH, 0, b"", small_win)
raw_small = deflate(longrange(1800), 9, -9)
for wb in (-8, -9, -10, -15):
    case(wb, 0, 4096, Z_NO_FLUSH, 0, b"", raw_small)
    case(wb, 17, 100, Z_NO_FLUSH, 0, b"", raw_small)
for wb in (-16, -1, -7, 7, 16, 47, 48, 63, 64, 100, 31, 32, 24, 40, -8, -15, 8):
    case(wb, 0, 4096, Z_NO_FLUSH, 0, b"", deflate(small["text"], 6, 15))
    case(wb, 0, 4096, Z_NO_FLUSH, 0, b"", gzip_manual(small["text"]))

# ---- 4. gzip headers -----------------------------------------------------------------------------------------------
gz_variants = [
    ("plain", {}),
    ("extra", dict(flags=4, extra=bytes(range(10)))),
    ("extra-big", dict(flags=4, extra=bytes(range(200)))),
    ("extra-empty", dict(flags=4, extra=b"")),
    ("name", dict(flags=8, name=b"file.txt")),
    ("name-long", dict(flags=8, name=b"n" * 100)),
    ("comment", dict(flags=16, comment=b"a comment")),
    ("comment-long", dict(flags=16, comment=b"c" * 90)),
    ("hcrc", dict(flags=2)),
    ("hcrc-bad", dict(flags=2, bad_hcrc=True)),
    ("all", dict(flags=4 | 8 | 16 | 2, extra=b"\x01\x02\x03", name=b"nm", comment=b"cm")),
    ("all-bad", dict(flags=4 | 8 | 16 | 2, extra=b"\x01\x02\x03", name=b"nm", comment=b"cm", bad_hcrc=True)),
    ("text-bit", dict(flags=1)),
    ("badflags", dict(flags=0x20)),
    ("mtime-big", dict(flags=0, mtime=0xfffffff0, xfl=4, os_=255)),
]
for gname, kw in gz_variants:
    stream = gzip_manual(small["text"], **kw)
    for wb in (31, 47, 15, 0):
        for (ic, oc) in ((0, 4096), (1, 7), (3, 1)):
            for opts in (0, OPT_HEAD):
                case(wb, ic, oc, Z_NO_FLUSH, opts, b"", stream)
    case(31, 5, 50, Z_FINISH, OPT_HEAD, b"", stream)
    case(31, 0, 4096, Z_BLOCK, OPT_HEAD, b"", stream)
    case(31, 1, 3, Z_TREES, OPT_HEAD, b"", stream)
    case(31, 0, 4096, Z_NO_FLUSH, OPT_HEAD | OPT_NOCHECK, b"", stream)
    for cut in (1, 5, 9, 11, 13, 15, 20):
        case(31, 0, 4096, Z_NO_FLUSH, OPT_HEAD, b"", stream[:cut])
        case(31, 1, 4096, Z_NO_FLUSH, OPT_HEAD, b"", stream[:cut])
# header with a non-gzip stream and GetHeader
case(15, 0, 4096, Z_NO_FLUSH, OPT_HEAD, b"", deflate(small["text"], 6, 15))
case(47, 0, 4096, Z_NO_FLUSH, OPT_HEAD, b"", deflate(small["text"], 6, 15))
case(-15, 0, 4096, Z_NO_FLUSH, OPT_HEAD, b"", deflate(small["text"], 6, -15))

# ---- 5. dictionaries -----------------------------------------------------------------------------------------------
D1 = b"the quick brown fox jumps over the lazy dog " * 4
D2 = bytes(range(256)) * 3
dtext = (b"the quick brown fox jumps over the lazy dog " * 6) + b"zlib inflate"
for zd in (D1, D2, b"x"):
    stream = deflate(dtext, 6, 15, 0, 8, zd)
    for (ic, oc) in ((0, 4096), (1, 3), (5, 40), (0, 1)):
        case(15, ic, oc, Z_NO_FLUSH, 0, zd, stream)          # right dictionary
        case(15, ic, oc, Z_NO_FLUSH, 0, D1 if zd != D1 else D2, stream)  # wrong dictionary
        case(15, ic, oc, Z_NO_FLUSH, 0, b"", stream)         # no dictionary: stops at Z_NEED_DICT
    case(15, 0, 4096, Z_NO_FLUSH, OPT_GETDICT, zd, stream)
    raw = deflate(dtext, 6, -15, 0, 8, zd)
    for (ic, oc) in ((0, 4096), (1, 3), (5, 40)):
        case(-15, ic, oc, Z_NO_FLUSH, OPT_SETDICT, zd, raw)     # raw stream, dictionary set at the start
        case(-15, ic, oc, Z_NO_FLUSH, 0, zd, raw)               # raw stream without it: wrong data
    case(-15, 0, 4096, Z_NO_FLUSH, OPT_SETDICT | OPT_GETDICT, zd, raw)
# a dictionary longer than the window
big = randbytes(40000)
stream = deflate(big[-3000:], 6, -15, 0, 8, big)
case(-15, 0, 4096, Z_NO_FLUSH, OPT_SETDICT | OPT_GETDICT, big, stream)
case(-9, 0, 4096, Z_NO_FLUSH, OPT_SETDICT | OPT_GETDICT, big[:700], deflate(big[500:900], 6, -9, 0, 8, big[:700]))
case(-15, 0, 4096, Z_NO_FLUSH, OPT_SETDICT | OPT_GETDICT, b"", deflate(small["text"], 6, -15))

# ---- 6. GetDictionary, Mark, Copy, Prime, NoCheck at the end of normal streams -------------------------------------
for name, wb, stream, size in mediumbases[:6] + bases[:4]:
    case(wb, 0, 4096, Z_NO_FLUSH, OPT_GETDICT, b"", stream)
    case(wb, 40, 90, Z_NO_FLUSH, OPT_GETDICT, b"", stream)
    case(wb, 40, 90, Z_NO_FLUSH, OPT_COPY, b"", stream)
    case(wb, 9, 11, Z_NO_FLUSH, OPT_COPY | OPT_GETDICT, b"", stream)
    case(wb, 40, 90, Z_NO_FLUSH, OPT_NOCHECK, b"", stream)
    case(wb, 0, 4096, Z_NO_FLUSH, OPT_PRIME, b"", stream)
    case(wb, 1, 1, Z_NO_FLUSH, OPT_PRIME, b"", stream)
for name, wb, stream, size in mediumbases:
    for (ic, oc) in ((20, 40), (0, 300), (7, 513)):
        case(wb, ic, oc, Z_NO_FLUSH, OPT_COPY | OPT_GETDICT, b"", stream)
# copy while the stream is in a fixed block (the source's comparison of unrelated pointers: a fault) and in stored blocks
for nm, stream in (("fixed", deflate(small["text"], 6, 15, 4)), ("stored", deflate(small["rand"], 0, 15)),
                   ("dyn", deflate(med["text"], 9, 15))):
    for (ic, oc) in ((1, 1), (4, 9), (0, 60), (30, 7)):
        case(15, ic, oc, Z_NO_FLUSH, OPT_COPY, b"", stream)

# ---- 7. corrupted streams -------------------------------------------------------------------------------------------
base_for_corruption = [
    ("z-text", 15, deflate(small["text"], 6)),
    ("z-rand", 15, deflate(small["rand"], 6)),
    ("z-fixed", 15, deflate(small["text"], 6, 15, 4)),
    ("z-stored", 15, deflate(small["rand"], 0)),
    ("z-long", 15, deflate(med["long"], 9)),
    ("raw-text", -15, deflate(small["text"], 6, -15)),
    ("gz-text", 31, gzip_manual(small["text"], flags=4 | 8 | 16 | 2, extra=b"ex", name=b"nm", comment=b"cm")),
    ("z-dict", 15, deflate(dtext, 6, 15, 0, 8, D1)),
]
hows = ["trunc1", "trunc4", "trunchalf", "append"] + ["flip%d" % i for i in (0, 1, 2, 3, 4, 5, 6, 8, 10, 13, 20, 30, 50, 80, 120)]
hows += ["set0_0", "set0_255", "set1_0", "set1_255", "set2_0", "set2_255", "set3_255"]
for name, wb, stream in base_for_corruption:
    for how in hows:
        cs = corrupt(stream, how)
        case(wb, 0, 4096, Z_NO_FLUSH, 0, D1, cs)
        case(wb, 3, 7, Z_NO_FLUSH, 0, D1, cs)
        if how in ("flip13", "flip30", "flip50", "trunchalf"):
            case(wb, 5, 100, Z_NO_FLUSH, OPT_SYNC | OPT_HEAD, D1, cs)
            case(wb, 0, 4096, Z_FINISH, OPT_HEAD, D1, cs)
# random corruption: many bytes changed
for t in range(60):
    name, wb, stream = base_for_corruption[t % len(base_for_corruption)]
    s = bytearray(stream)
    for _ in range(1 + t % 4):
        s[rng.randrange(len(s))] = rng.randrange(256)
    case(wb, rng.choice((0, 1, 3, 17)), rng.choice((1, 5, 64, 4096)), Z_NO_FLUSH, rng.choice((0, 1, 64, 65)), D1, bytes(s))
# pure garbage
for t in range(50):
    n = rng.randrange(0, 40)
    g = randbytes(n)
    case(rng.choice((15, -15, 31, 47, 9)), rng.choice((0, 1, 5)), rng.choice((2, 4096)), Z_NO_FLUSH, rng.choice((0, 1)), b"", g)
for t in range(24):
    # raw deflate garbage that starts with a valid block header: stored, fixed, dynamic
    g = bytes([rng.choice((0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x0d, 0xed, 0xfd, 0xe5))]) + randbytes(rng.randrange(0, 60))
    case(-15, rng.choice((0, 1, 6)), rng.choice((2, 4096)), Z_NO_FLUSH, 0, b"", g)

# ---- 8. dynamic-table errors made by hand (raw deflate blocks) -----------------------------------------------------
def bits_to_bytes(bits):
    while len(bits) % 8:
        bits.append(0)
    return bytes(sum(bits[i + j] << j for j in range(8)) for i in range(0, len(bits), 8))

def put(bits, value, n):
    for i in range(n):
        bits.append((value >> i) & 1)

def dyn_header(hlit, hdist, hclen, clens, rest=lambda b: None, last=1):
    b = []
    put(b, last, 1); put(b, 2, 2)
    put(b, hlit, 5); put(b, hdist, 5); put(b, hclen, 4)
    for c in clens:
        put(b, c, 3)
    rest(b)
    return bits_to_bytes(b)

for hlit in (0, 29, 30, 31):
    for hdist in (0, 29, 30, 31):
        case(-15, 0, 4096, Z_NO_FLUSH, 0, b"", dyn_header(hlit, hdist, 15, [2] * 19))
        case(-15, 1, 3, Z_NO_FLUSH, 0, b"", dyn_header(hlit, hdist, 15, [2] * 19))
case(-15, 0, 4096, Z_NO_FLUSH, 0, b"", dyn_header(0, 0, 0, [0] * 4))
case(-15, 0, 4096, Z_NO_FLUSH, 0, b"", dyn_header(0, 0, 15, [0] * 19))
case(-15, 0, 4096, Z_NO_FLUSH, 0, b"", dyn_header(0, 0, 15, [1] * 19))
case(-15, 0, 4096, Z_NO_FLUSH, 0, b"", dyn_header(0, 0, 15, [3, 3, 3, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]))
# stored block with bad length complement and good ones
case(-15, 0, 4096, Z_NO_FLUSH, 0, b"", bytes([1, 5, 0, 0, 0]) + b"hello")
case(-15, 0, 4096, Z_NO_FLUSH, 0, b"", bytes([1, 5, 0, 0xfa, 0xff]) + b"hello")
case(-15, 1, 2, Z_NO_FLUSH, 0, b"", bytes([0, 5, 0, 0xfa, 0xff]) + b"hello" + bytes([1, 0, 0, 0xff, 0xff]))
case(-15, 1, 2, Z_TREES, 0, b"", bytes([0, 5, 0, 0xfa, 0xff]) + b"hello" + bytes([1, 0, 0, 0xff, 0xff]))
case(-15, 3, 1, Z_BLOCK, 0, b"", bytes([0, 5, 0, 0xfa, 0xff]) + b"hello" + bytes([1, 0, 0, 0xff, 0xff]))
case(-15, 0, 4096, Z_NO_FLUSH, 0, b"", bytes([7]))
case(-15, 0, 4096, Z_NO_FLUSH, 0, b"", bytes([6]))

# ---- 9. sync flush streams and inflateSync ---------------------------------------------------------------------------
def synced(parts):
    c = zlib.compressobj(6, zlib.DEFLATED, 15)
    b = b""
    for p in parts:
        b += c.compress(p) + c.flush(zlib.Z_SYNC_FLUSH)
    return b + c.flush()

sy = synced([text(150), randbytes(60), text(90)])
for (ic, oc) in ((0, 4096), (1, 3), (7, 11)):
    case(15, ic, oc, Z_NO_FLUSH, 0, b"", sy)
    case(15, ic, oc, Z_SYNC_FLUSH, 0, b"", sy)
for pos in (5, 12, 40, 100, 150, 200):
    cs = bytearray(sy)
    cs[pos % len(cs)] ^= 0x55
    for (ic, oc) in ((0, 4096), (9, 20)):
        case(15, ic, oc, Z_NO_FLUSH, OPT_SYNC, b"", bytes(cs))
        case(15, ic, oc, Z_BLOCK, OPT_SYNC, b"", bytes(cs))
        case(15, ic, oc, Z_NO_FLUSH, OPT_SYNC | OPT_NOCHECK, b"", bytes(cs))
# sync on raw / gzip streams after an error
cr = zlib.compressobj(6, zlib.DEFLATED, -15)
rawsy = cr.compress(text(120)) + cr.flush(zlib.Z_FULL_FLUSH) + cr.compress(text(80)) + cr.flush()
for pos in (3, 10, 30):
    cs = bytearray(rawsy)
    cs[pos % len(cs)] ^= 0xa5
    case(-15, 0, 4096, Z_NO_FLUSH, OPT_SYNC, b"", bytes(cs))
    case(-15, 5, 7, Z_NO_FLUSH, OPT_SYNC, b"", bytes(cs))

# ---- 10. priming ------------------------------------------------------------------------------------------------------
for wb in (-15, 15, 31, 47):
    for st in (deflate(small["text"], 6, -15), deflate(small["text"], 6, 15), gzip_manual(small["text"])):
        case(wb, 0, 4096, Z_NO_FLUSH, OPT_PRIME, b"", st)
        case(wb, 1, 3, Z_NO_FLUSH, OPT_PRIME | OPT_HEAD, b"", st)

# ---- 11. no output space / no input ----------------------------------------------------------------------------------
for fl in (Z_NO_FLUSH, Z_FINISH):
    case(15, 0, 1, fl, 0, b"", deflate(small["text"], 6))
    case(15, 1, 1, fl, 0, b"", b"")
    case(-15, 1, 1, fl, 0, b"", b"")
    case(31, 0, 5, fl, OPT_HEAD, b"", b"")

# ---- 12. zlib headers with a window size above 15 (CINFO 8..15), with and without wbits 0 -------------------------------
for cinfo in range(0, 16):
    cmf = (cinfo << 4) | 8
    flg = 0
    while ((cmf << 8) | flg) % 31:
        flg += 1
    hdr = bytes([cmf, flg])
    body = deflate(small["text"], 6, -15)
    for wb in (0, 15, 9):
        case(wb, 0, 4096, Z_NO_FLUSH, 0, b"", hdr + body + struct.pack(">I", zlib.adler32(small["text"])))
# a CM other than 8
for cm in (0, 7, 9, 15):
    cmf = 0x70 | cm
    flg = 0
    while ((cmf << 8) | flg) % 31:
        flg += 1
    case(15, 0, 4096, Z_NO_FLUSH, 0, b"", bytes([cmf, flg]) + b"\x03\x00")

# ---- 13. long streams: the window slides (more than 32K of output), exact-size and oversize output buffers, whole-stream
# calls as uncompress() makes them, zlib, gzip and raw wrappers ----------------------------------------------------------
def mixed(n):
    b = bytearray()
    while len(b) < n:
        r = rng.random()
        if r < 0.5:
            b += text(rng.randrange(20, 300))
        elif r < 0.7:
            b += randbytes(rng.randrange(10, 100))
        elif r < 0.9 and len(b) > 1000:
            st = rng.randrange(0, len(b) - 500)
            b += b[st:st + rng.randrange(20, 400)]
        else:
            b += bytes(rng.randrange(1, 300))
    return bytes(b[:n])

# Whole stream in one call (the shape of uncompress()): the Lean heap is a chain of closures that keeps every version of a
# written block, so one call that writes N bytes costs about N * N bytes of memory; the sizes are kept below that.
for n in (9000, 20000):
    data = mixed(n)
    for wbits_inf, form in ((15, 15), (31, 31), (-15, -15), (47, 31), (47, 15), (0, 15)):
        stream = deflate(data, 6, form)
        for oc in (n, n + 1):
            case(wbits_inf, 0, oc, Z_NO_FLUSH, 0, b"", stream)
        case(wbits_inf, 0, n, Z_FINISH, 0, b"", stream)
        case(wbits_inf, 0, n + 1, Z_FINISH, OPT_GETDICT, b"", stream)
    gz = gzip_manual(data, flags=4 | 8 | 16 | 2, extra=b"xy", name=b"n", comment=b"c")
    case(31, 0, n, Z_FINISH, OPT_HEAD, b"", gz)
    for lvl in (0, 1, 9):
        case(15, 0, n + 1, Z_FINISH, 0, b"", deflate(data, lvl, 15))
        case(31, 0, n + 1, Z_FINISH, 0, b"", deflate(data, lvl, 31))
        case(-15, 0, n + 1, Z_FINISH, 0, b"", deflate(data, lvl, -15))

# The window slides: more than 32K of output, small output buffers, every wrapper.
for n in (33000, 70000):
    data = mixed(n)
    for wbits_inf, form in ((15, 15), (31, 31), (-15, -15), (47, 31), (47, 15), (0, 15)):
        stream = deflate(data, 6, form)
        case(wbits_inf, 0, 8192, Z_NO_FLUSH, OPT_GETDICT, b"", stream)
        case(wbits_inf, 4000, 5000, Z_NO_FLUSH, 0, b"", stream)
        case(wbits_inf, 1000, 258, Z_NO_FLUSH, OPT_COPY, b"", stream)
    gz = gzip_manual(data, flags=4 | 8 | 16 | 2, extra=b"xy", name=b"n", comment=b"c")
    case(31, 3000, 7000, Z_NO_FLUSH, OPT_HEAD | OPT_GETDICT, b"", gz)
    for lvl in (0, 1, 9):
        case(15, 6000, 6000, Z_NO_FLUSH, 0, b"", deflate(data, lvl, 15))
        case(31, 6000, 6000, Z_NO_FLUSH, 0, b"", deflate(data, lvl, 31))

for line in out:
    print(line)
