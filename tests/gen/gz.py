#!/usr/bin/env python3
"""Inputs for the gz*.c and uncompr.c differential test, written to stdout. Deterministic (fixed seed).

Lines: "gz OP OP ..." (a scenario on temporary files; the output is one token per OP joined by '|') and
"unc HEX DESTLEN [SRCLEN]" (uncompress2).  OPs (fields separated by ':', '-' is an empty hex string):
  put:NAME:HEX  mkdir:NAME  fsize:N (RLIMIT_FSIZE, 0 = none)  dump:NAME
  open:H:NAME:MODE  dopen:H:NAME:K:MODE (K = r w a c bad)  buffer:H:N  close:H closer:H closew:H
  write:H:HEX fwrite:H:SIZE:HEX putc:H:C puts:H:HEX printf:H:K:ARGS.. flush:H:F setparams:H:L:S
  read:H:N fread:H:SIZE:N gets:H:LEN getc:H ungetc:H:C seek:H:OFF:WHENCE tell:H offset:H rewind:H eof:H
  direct:H error:H clearerr:H
Handles H are 0..3; a handle that was never opened (or whose open failed) is the NULL gzFile.
Inputs avoid the known bug of zlib that no patch fixes (x.next left dangling, docs/design/external-io.md). Section 6
seeks right after a gzungetc at position 0, which the unpatched gzseek64 overflowed on (patch 0002); the translation of
the unpatched C faults there, so those lines tell the two apart. The gz_fetch overread after a partial read that then
fails (patch 0003) needs a read() the file model cannot produce; tests/regression/gzread-transparent-stale-next
covers it on the C side.
"""
import random
import zlib
import struct

rnd = random.Random(20260105)
out = []


def hx(b):
    return b.hex() if len(b) else "-"


def line(*ops):
    out.append("gz " + " ".join(ops))


def gzmember(data, level=6, strategy=zlib.Z_DEFAULT_STRATEGY):
    c = zlib.compressobj(level, zlib.DEFLATED, 31, 8, strategy)
    return c.compress(data) + c.flush()


def text(n):
    words = [b"alpha", b"beta", b"gamma", b"delta", b"zlib", b"gz", b"line", b"\n", b" ", b"x"]
    r = bytearray()
    while len(r) < n:
        r += rnd.choice(words)
        if rnd.random() < 0.15:
            r += b"\n"
    return bytes(r[:n])


def rand(n):
    return bytes(rnd.randrange(256) for _ in range(n))


def runs(n):
    return bytes(((i // 37) * 5) & 0xFF for i in range(n))


def lines_data(n, maxlen=30):
    r = bytearray()
    while len(r) < n:
        r += bytes(rnd.choice(b"abcdefgh ") for _ in range(rnd.randrange(0, maxlen))) + b"\n"
    return bytes(r[:n])


SIZES = [0, 1, 2, 7, 8, 9, 15, 16, 100, 255, 1000, 4095, 4096, 4097, 8191, 8192, 8193, 16384, 20000]
DATAS = [("text", text), ("rand", rand), ("runs", runs)]

# --- 1. write then read back: modes, sizes, buffer sizes, read patterns
for n in SIZES:
    for kind, fn in DATAS:
        if kind != "text" and n not in (1, 100, 4097, 8193, 20000):
            continue
        d = fn(n)
        line("open:0:f:wb", "write:0:" + hx(d), "close:0", "dump:f", "open:1:f:rb", "read:1:" + str(n + 5), "eof:1", "close:1")
    d = text(n)
    line("open:0:f:wb", "write:0:" + hx(d), "close:0", "open:1:f:rb", "read:1:" + str(max(n // 2, 1)),
         "read:1:" + str(n), "read:1:10", "eof:1", "tell:1", "close:1")

for mode in ["wb0", "wb1", "wb2", "wb3", "wb4", "wb5", "wb6", "wb7", "wb8", "wb9", "w", "wbf", "wbh", "wbR", "wbF", "w9f",
             "wbe", "wb6x", "wb0F", "w1h", "wbN", "wbG", "wb+", "w5R", "wxb"]:
    d = text(3000) + rand(300)
    line("open:0:f:" + mode, "write:0:" + hx(d), "close:0", "dump:f", "open:1:f:rb", "read:1:4000", "close:1")

for bsz in [0, 1, 7, 8, 9, 16, 33, 100, 1000, 8192, 65536]:
    d = text(5000)
    line("open:0:f:wb", "buffer:0:" + str(bsz), "write:0:" + hx(d), "buffer:0:100", "close:0", "dump:f",
         "open:1:f:rb", "buffer:1:" + str(bsz), "read:1:5000", "buffer:1:100", "close:1")
for bsz in [4294967295, 2147483648, 4294967294]:
    line("open:0:f:wb", "buffer:0:" + str(bsz), "close:0", "open:1:f:wb", "write:1:" + hx(b"abc"), "buffer:1:8", "close:1")

# small buffers force many refills / flushes
for bsz in [8, 9, 17]:
    for kind, fn in DATAS:
        d = fn(1500)
        line("open:0:f:wb", "buffer:0:" + str(bsz), "write:0:" + hx(d), "flush:0:2", "write:0:" + hx(d[:100]),
             "flush:0:3", "close:0", "dump:f", "open:1:f:rb", "buffer:1:" + str(bsz), "read:1:3000", "close:1")
        line("open:0:f:wb", "buffer:0:" + str(bsz), "write:0:" + hx(d), "close:0", "open:1:f:rb",
             "buffer:1:" + str(bsz), *(["read:1:37"] * 5), "tell:1", "offset:1", "close:1")

# --- 2. getc / putc / puts / gets / fread / fwrite
d = text(300)
line("open:0:f:wb", *["putc:0:" + str(b) for b in d[:200]], "putc:0:300", "putc:0:-1", "close:0", "open:1:f:rb",
     *(["getc:1"] * 210), "eof:1", "close:1")
line("open:0:f:wb", "buffer:0:8", *["putc:0:" + str(b) for b in b"hello world, this is putc"], "close:0", "dump:f")
line("open:0:f:wb", "puts:0:" + hx(b"hello"), "puts:0:" + hx(b"\n"), "puts:0:" + hx(b"line two\n"), "puts:0:-", "close:0",
     "open:1:f:rb", "gets:1:100", "gets:1:100", "gets:1:100", "close:1")
for L in [1, 2, 3, 5, 10, 31, 32, 33, 100, 0, -1]:
    dd = lines_data(600)
    line("open:0:f:wb", "write:0:" + hx(dd), "close:0", "open:1:f:rb", *(["gets:1:" + str(L)] * 12), "eof:1", "tell:1", "close:1")
line("open:0:f:wb", "write:0:" + hx(b"no newline at the end"), "close:0", "open:1:f:rb", "gets:1:100", "gets:1:100", "eof:1", "close:1")
line("open:0:f:wb", "buffer:0:8", "write:0:" + hx(lines_data(300)), "close:0", "open:1:f:rb", "buffer:1:8",
     *(["gets:1:40"] * 12), "close:1")
for size, items in [(1, 10), (4, 25), (10, 7), (0, 5), (7, 0), (3, 1000), (100, 200)]:
    dd = text(500)
    line("open:0:f:wb", "fwrite:0:" + str(size) + ":" + hx(dd), "close:0", "dump:f", "open:1:f:rb",
         "fread:1:" + str(size) + ":" + str(items), "fread:1:" + str(size) + ":" + str(items), "eof:1", "close:1")
line("open:0:f:wb", "fwrite:0:3:" + hx(b"abcdefgh"), "close:0", "dump:f")
line("open:0:f:wb", "write:0:" + hx(text(100)), "close:0", "open:1:f:rb", "fread:1:4611686018427387905:4", "error:1", "close:1")
line("open:0:f:wb", "write:0:" + hx(text(100)), "close:0", "open:1:f:rb", "fread:1:3:6148914691236517206", "error:1", "read:1:5", "close:1")
line("open:0:f:wb", "fwrite:0:4611686018427387905:" + hx(b"ab"), "error:0", "close:0")

# --- 3. printf
FM = {
    0: [], 1: ["i42"], 2: ["i7", "i7", "i7"], 3: ["s" + b"ab".hex(), "s" + b"cd".hex()],
    4: ["u255", "u255", "u255", "u8"], 5: ["l-5", "m99"], 6: ["i65", "i66"], 7: ["s" + b"abcdef".hex(), "s" + b"xy".hex(), "s" + b"zz".hex()],
    8: ["i5", "i-5"], 9: [], 10: ["u255", "u8"], 11: ["s" + b"long string".hex()], 12: ["i0", "i42"],
}
for k, args in FM.items():
    line("open:0:f:wb", "printf:0:%d:%s" % (k, ":".join(args)) if args else "printf:0:%d" % k, "close:0", "dump:f")
for v in ["i-2147483648", "i2147483647", "i0", "i-1", "i100000"]:
    line("open:0:f:wb", "printf:0:2:%s:%s:%s" % (v, v, v), "printf:0:1:" + v, "printf:0:8:%s:%s" % (v, v), "close:0", "dump:f")
for v in ["u0", "u4294967295", "u1", "u305419896"]:
    line("open:0:f:wb", "printf:0:4:%s:%s:%s:%s" % (v, v, v, v), "printf:0:10:%s:%s" % (v, v), "close:0", "dump:f")
line("open:0:f:wb", "printf:0:5:l-9223372036854775808:m4611686018427387904", "printf:0:5:l9223372036854775807:m0", "close:0", "dump:f")
for n in [100, 1000, 4000, 8000, 8190, 8191, 8192, 8193, 9000, 20000]:
    s = ("s" + (b"q" * n).hex())
    line("open:0:f:wb", "printf:0:11:" + s, "printf:0:11:" + s, "close:0", "dump:f")
    line("open:0:f:wb", "buffer:0:16", "printf:0:11:" + "s" + (b"q" * min(n, 40)).hex(), "printf:0:11:" + "s" + (b"w" * 15).hex(),
         "printf:0:11:" + "s" + (b"e" * 16).hex(), "close:0", "dump:f")
line("open:0:f:wb", "write:0:" + hx(text(5000)), "printf:0:11:s" + (b"r" * 7000).hex(), "write:0:" + hx(b"tail"), "close:0",
     "open:1:f:rb", "read:1:20000", "close:1")
# a failing vsnprintf (C: "%3000000000d" -> -1 EOVERFLOW; model: oracle failure): gzprintf returns 0, file unchanged
line("open:0:f:wb", "printf:0:1:i5", "printf:0:13:i7", "printf:0:1:i9", "close:0", "dump:f")
line("open:0:f:wb", "buffer:0:8", "write:0:" + hx(b"abc"), "printf:0:13:i1", "error:0", "puts:0:" + hx(b"z"), "close:0", "dump:f")
line("open:0:f:wbT", "printf:0:2:i1:i2:i3", "write:0:" + hx(b"raw"), "puts:0:" + hx(b"s"), "putc:0:65", "close:0", "dump:f")

# --- 4. transparent reads, gzdirect, gzip-only
for n in [0, 1, 2, 3, 4, 5, 100, 8192, 8193, 20000]:
    d = text(n)
    line("put:f:" + hx(d), "open:0:f:rb", "direct:0", "read:0:" + str(n + 3), "direct:0", "eof:0", "close:0")
    line("put:f:" + hx(d), "open:0:f:rb", "read:0:1", "read:0:7", "getc:0", "gets:0:50", "tell:0", "offset:0", "close:0")
for hdr in [b"\x1f", b"\x1f\x8b", b"\x1f\x8b\x08", b"\x1f\x8b\x08\x00", b"\x1f\x8b\x08\x20", b"\x1f\x8b\x09\x00", b"\x1f\x8c\x08\x00", b"\x1e\x8b\x08\x00"]:
    d = hdr + text(40)
    line("put:f:" + hx(d), "open:0:f:rb", "direct:0", "read:0:100", "error:0", "close:0")
d = text(2000)
line("put:f:" + hx(d), "open:0:f:rbG", "read:0:100", "error:0", "direct:0", "close:0")
line("put:f:" + hx(gzmember(d)), "open:0:f:rb", "direct:0", "read:0:3000", "direct:0", "close:0")
line("put:f:" + hx(gzmember(d)), "open:0:f:rb", "read:0:10", "direct:0", "close:0")
line("put:f:" + hx(gzmember(d)), "open:0:f:rbG", "read:0:3000", "direct:0", "close:0")
line("open:0:f:wbT", "write:0:" + hx(d), "close:0", "open:1:f:rb", "direct:1", "read:1:5000", "close:1", "dump:f")
line("open:0:f:rbT")      # a transparent request when reading is refused
line("open:0:f:wbG")      # 'G' when writing is refused
line("put:f:" + hx(b"abc"), "open:0:f:r", "open:1:f:rT", "open:2:f:rG", "close:0", "close:2")

# header prefixes that are exactly 3 and 4 bytes long (the test avail_in > 3 of gz_look)
for pre in [b"\x1f\x8b\x08", b"\x1f\x8b\x08\x00", b"\x1f\x8b\x08\x20", b"\x1f\x8b\x08\x21"]:
    line("put:f:" + hx(pre), "open:0:f:rb", "direct:0", "read:0:10", "error:0", "eof:0", "close:0")
# gzgets with a one-byte buffer budget (len == 2) at and after the end of the data
for src in [b"ab\n", gzmember(b"ab\n")]:
    line("put:f:" + hx(src), "open:0:f:rb", *(["gets:0:2"] * 5), "eof:0", "close:0")

# --- 5. gzip streams made by zlib: concatenation, trailing garbage, truncation, corruption
base = text(3000)
g1 = gzmember(base[:1000])
g2 = gzmember(base[1000:])
line("put:f:" + hx(g1 + g2), "open:0:f:rb", "read:0:5000", "eof:0", "error:0", "close:0")
line("put:f:" + hx(g1 + g2), "open:0:f:rb", *(["read:0:777"] * 6), "close:0")
line("put:f:" + hx(g1 + g2), "open:0:f:rb", "buffer:0:8", *(["read:0:777"] * 6), "close:0")
line("put:f:" + hx(g1 + g2), "open:0:f:rb", "buffer:0:8", *(["getc:0"] * 30), "close:0")
for tail in [b"\x00", b"\x00" * 10, b"garbage!", b"\x1f\x8b", b"\x1f\x8b\x08\x00zzzzzz", b"\x1f\x8b\x08\x00"]:
    line("put:f:" + hx(g1 + tail), "open:0:f:rb", "read:0:5000", "read:0:5", "error:0", "eof:0", "close:0")
    line("put:f:" + hx(g1 + g2 + tail), "open:0:f:rb", "read:0:5000", "read:0:5", "error:0", "close:0")
for cut in [1, 5, 9, 10, 11, 12, 20, len(g1) // 2, len(g1) - 9, len(g1) - 8, len(g1) - 5, len(g1) - 1]:
    line("put:f:" + hx(g1[:cut]), "open:0:f:rb", "read:0:5000", "error:0", "read:0:5", "error:0", "close:0")
    line("put:f:" + hx(g1[:cut]), "open:0:f:rb", "buffer:0:8", "read:0:5000", "error:0", "gets:0:50", "close:0")
for pos in [0, 1, 2, 3, 4, 9, 10, 15, len(g1) // 2, len(g1) - 8, len(g1) - 4, len(g1) - 1]:
    for xor in [0x01, 0x80, 0xFF]:
        bb = bytearray(g1 + g2)
        bb[pos] ^= xor
        line("put:f:" + hx(bytes(bb)), "open:0:f:rb", "read:0:5000", "error:0", "read:0:100", "eof:0", "close:0")
bb = bytearray(g1)
bb[len(bb) // 2] ^= 0x40
line("put:f:" + hx(bytes(bb)), "open:0:f:rb", "read:0:100", "read:0:100", "error:0", "clearerr:0", "error:0", "read:0:100", "close:0")
line("put:f:" + hx(bytes(bb)), "open:0:f:rb", "buffer:0:8", "gets:0:30", "gets:0:30", "gets:0:30", "error:0", "ungetc:0:65", "getc:0", "close:0")
line("put:f:" + hx(g1[:-3]), "open:0:f:rb", "read:0:2000", "seek:0:0:0", "read:0:10", "rewind:0", "read:0:10", "error:0", "close:0")
# header flags: extra, name, comment, hcrc (made by hand)
body = zlib.compressobj(6, zlib.DEFLATED, -15)
raw = body.compress(base[:500]) + body.flush()
crc = struct.pack("<II", zlib.crc32(base[:500]) & 0xFFFFFFFF, 500)
for flg, extra in [(0x04, struct.pack("<H", 5) + b"12345"), (0x08, b"name\x00"), (0x10, b"comment\x00"), (0x02, b"\x00\x00"), (0x1e, struct.pack("<H", 2) + b"ab" + b"n\x00" + b"c\x00" + b"\x00\x00")]:
    m = b"\x1f\x8b\x08" + bytes([flg]) + b"\x00" * 4 + b"\x00\x03" + extra + raw + crc
    line("put:f:" + hx(m), "open:0:f:rb", "read:0:1000", "error:0", "close:0")
# bad crc / length trailer
m = b"\x1f\x8b\x08\x00" + b"\x00" * 4 + b"\x00\x03" + raw + struct.pack("<II", 0, 500)
line("put:f:" + hx(m), "open:0:f:rb", "read:0:1000", "error:0", "close:0")
m = b"\x1f\x8b\x08\x00" + b"\x00" * 4 + b"\x00\x03" + raw + struct.pack("<II", zlib.crc32(base[:500]) & 0xFFFFFFFF, 7)
line("put:f:" + hx(m), "open:0:f:rb", "read:0:1000", "error:0", "close:0")
# a gz file with only junk after an empty first read
line("put:f:" + hx(b"\x1f\x8b\x08\x00zzzzzzzzzz"), "open:0:f:rb", "read:0:100", "error:0", "close:0")

# --- 6. seek, tell, offset, rewind (reading gzip, reading raw, writing)
big = text(20000)
gzbig = gzmember(big)
for src, name in [(gzbig, "gz"), (big, "raw")]:
    p = "put:f:" + hx(src)
    for off, wh in [(0, 0), (5, 0), (100, 0), (8192, 0), (19999, 0), (20000, 0), (25000, 0), (-1, 0), (100, 1), (-1, 1), (0, 1),
                    (1, 2), (0, 2), (-5, 1), (3, 7), (3, -1)]:
        line(p, "open:0:f:rb", "read:0:50", "seek:0:%d:%d" % (off, wh), "tell:0", "offset:0", "read:0:30", "tell:0", "eof:0", "close:0")
    line(p, "open:0:f:rb", "seek:0:7000:0", "tell:0", "getc:0", "seek:0:-3:1", "getc:0", "getc:0", "getc:0", "getc:0", "tell:0", "close:0")
    line(p, "open:0:f:rb", "read:0:5000", "seek:0:100:0", "read:0:10", "seek:0:-10:1", "read:0:10", "seek:0:0:0", "read:0:10", "close:0")
    line(p, "open:0:f:rb", "buffer:0:8", "read:0:500", "seek:0:100:0", "read:0:10", "seek:0:-10:1", "read:0:10", "seek:0:19000:0", "read:0:5000", "eof:0", "seek:0:5:0", "read:0:5", "close:0")
    line(p, "open:0:f:rb", "seek:0:30000:0", "read:0:10", "eof:0", "tell:0", "rewind:0", "tell:0", "read:0:10", "eof:0", "close:0")
    line(p, "open:0:f:rb", "seek:0:10:1", "seek:0:10:1", "tell:0", "read:0:5", "gets:0:20", "seek:0:-100:1", "tell:0", "close:0")
    line(p, "open:0:f:rb", "read:0:100", "rewind:0", "rewind:0", "read:0:100", "gets:0:10", "rewind:0", "gets:0:10", "close:0")
    line(p, "open:0:f:rb", "direct:0", "seek:0:0:1", "tell:0", "read:0:3", "close:0")
    line(p, "open:0:f:rb", "seek:0:0:1", "tell:0", "read:0:3", "close:0")
    line(p, "open:0:f:rb", "getc:0", "getc:0", "ungetc:0:90", "getc:0", "getc:0", "tell:0", "ungetc:0:1", "ungetc:0:2", "tell:0", "read:0:4", "close:0")
    line(p, "dopen:0:f:r:rb", "read:0:100", "offset:0", "tell:0", "close:0")
    line(p, "dopen:0:f:r:rb", "seek:0:100:0", "read:0:10", "seek:0:0:0", "read:0:10", "close:0")
line("put:f:" + hx(gzbig), "open:0:f:rb", "seek:0:-1:0", "seek:0:-9223372036854775808:0", "seek:0:9223372036854775807:0",
     "seek:0:9223372036854775807:1", "tell:0", "close:0")
line("put:f:" + hx(big), "open:0:f:rb", "read:0:10", "seek:0:9223372036854775807:1", "seek:0:-9223372036854775808:1", "tell:0", "close:0")
# gzseek right after gzungetc at position 0 (x.pos = -1): the unpatched gzseek64 overflowed in GZ_OFF_MAX - pos
# (SEEK_CUR) and in pos - x.pos (SEEK_SET to GZ_OFF_MAX); patch 0002, upstream PR 1361
# (an accepted target near GZ_OFF_MAX only for gzip input: on a raw file it is an lseek whose result depends on the
# file system's maximum file size)
for src in (gzbig, big):
    p = "put:f:" + hx(src)
    line(p, "open:0:f:rb", "ungetc:0:81", "seek:0:1:1", "tell:0", "read:0:5", "close:0")
    line(p, "open:0:f:rb", "ungetc:0:81", "seek:0:0:1", "seek:0:-1:1", "tell:0", "getc:0", "close:0")
    line(p, "open:0:f:rb", "ungetc:0:81", "seek:0:9223372036854775807:0", "tell:0", "getc:0", "close:0")
    line(p, "open:0:f:rb", "ungetc:0:81", "seek:0:-9223372036854775808:1", "seek:0:5:0", "tell:0", "read:0:3", "close:0")
    line(p, "open:0:f:rb", "ungetc:0:81", "seek:0:100:0", "tell:0", "read:0:5", "close:0")
p = "put:f:" + hx(gzbig)
line(p, "open:0:f:rb", "ungetc:0:81", "seek:0:9223372036854775806:0", "tell:0", "close:0")
line(p, "open:0:f:rb", "ungetc:0:81", "seek:0:9223372036854775807:1", "tell:0", "seek:0:5:0", "tell:0", "read:0:3", "close:0")

# gzseek on write handles (zero fill), tell, backward seeks
for off in [0, 1, 5, 8191, 8192, 8193, 20000, 70000]:
    line("open:0:f:wb", "write:0:" + hx(b"head"), "seek:0:%d:1" % off, "tell:0", "write:0:" + hx(b"tail"), "tell:0", "close:0",
         "dump:f" if off < 9000 else "open:1:f:rb", *([] if off < 9000 else ["read:1:100000", "close:1"]))
line("open:0:f:wb", "write:0:" + hx(b"head"), "seek:0:2:0", "seek:0:-1:1", "seek:0:4:0", "tell:0", "close:0", "dump:f")
line("open:0:f:wb", "seek:0:100:0", "close:0", "open:1:f:rb", "read:1:1000", "close:1")
line("open:0:f:wb", "buffer:0:8", "write:0:" + hx(b"head"), "seek:0:100:1", "putc:0:65", "printf:0:1:i3", "puts:0:" + hx(b"zz"), "close:0", "open:1:f:rb", "read:1:1000", "close:1")
line("open:0:f:wb", "seek:0:5:0", "flush:0:2", "setparams:0:1:1", "close:0", "open:1:f:rb", "read:1:100", "close:1")
line("open:0:f:wbT", "write:0:" + hx(b"head"), "seek:0:10:1", "write:0:" + hx(b"x"), "tell:0", "offset:0", "close:0", "dump:f")
line("open:0:f:wb", "write:0:" + hx(b"head"), "offset:0", "tell:0", "flush:0:2", "offset:0", "close:0")

# --- 7. append mode, multiple members
for m1, m2 in [("wb", "ab"), ("wb1", "ab9"), ("wbT", "a"), ("wb", "aT")]:
    line("open:0:f:" + m1, "write:0:" + hx(text(500)), "close:0", "open:1:f:" + m2, "write:1:" + hx(text(300)), "close:1",
         "dump:f", "open:2:f:rb", "read:2:2000", "read:2:2000", "close:2")
line("open:0:f:ab", "write:0:" + hx(b"abc"), "tell:0", "offset:0", "close:0", "dump:f")
line("put:f:" + hx(b"xyz"), "open:0:f:ab", "write:0:" + hx(b"abc"), "close:0", "dump:f", "open:1:f:rb", "read:1:100", "close:1")
line("open:0:f:ab", "close:0", "dump:f")
line("open:0:f:wb", "close:0", "dump:f", "open:1:f:rb", "read:1:10", "eof:1", "close:1")
line("open:0:f:wb", "flush:0:2", "flush:0:2", "close:0", "dump:f")
line("open:0:f:wb", "write:0:" + hx(b"abc"), "flush:0:4", "write:0:" + hx(b"def"), "flush:0:4", "close:0", "dump:f", "open:1:f:rb", "read:1:100", "close:1")

# --- 8. open failures, modes, descriptors
line("open:0:missing:rb", "open:1:missing:r", "open:2:d:wb")
line("mkdir:d", "open:0:d:rb", "read:0:10", "error:0", "close:0")
line("mkdir:d", "open:0:d:wb", "open:1:d:ab", "open:2:d:r", "gets:2:10", "getc:2", "error:2", "close:2")
line("mkdir:d", "open:0:d:rb", "direct:0", "error:0", "close:0")
line("put:f:" + hx(b"x"), "open:0:f:wbx", "open:1:f:rbx", "open:2:new:wbx", "write:2:" + hx(b"q"), "close:2", "open:3:new:wbx")
line("open:0:f:-", "open:1:f:b", "open:2:f:9", "open:3:f:+")
line("open:0:f:wr", "write:0:" + hx(b"abc"), "close:0", "dump:f")
line("open:0:f:rw", "close:0", "dump:f")
line("open:0:f:r+", "open:1:f:w+", "open:2:f:a+")
line("open:0:f:w5w", "write:0:" + hx(b"abc"), "close:0", "dump:f")
line("open:0:f:wb99", "write:0:" + hx(text(100)), "close:0", "open:1:f:rb", "read:1:200", "close:1")
line("put:f:" + hx(b"abc"), "dopen:0:f:bad:rb", "dopen:1:f:r:rb", "read:1:10", "close:1", "dopen:2:g:w:wb", "write:2:" + hx(b"xyz"), "close:2", "dump:g")
line("dopen:0:g:a:ab", "write:0:" + hx(b"1"), "close:0", "dopen:1:g:a:ab", "write:1:" + hx(b"2"), "close:1", "dump:g")
line("put:f:" + hx(b"abc"), "dopen:0:f:r:rbN", "read:0:10", "close:0", "dopen:1:f:r:rbe", "read:1:10", "close:1")
line("dopen:0:g:w:wbN", "write:0:" + hx(b"z"), "close:0", "dopen:1:g:w:wbe", "write:1:" + hx(b"z"), "close:1", "dump:g")
line("put:f:" + hx(b"abc"), "dopen:0:f:w:rb", "read:0:10", "error:0", "close:0")
line("put:f:" + hx(b"abc"), "dopen:0:f:r:wb", "write:0:" + hx(b"zzz"), "close:0", "error:0")
line("put:f:" + hx(b"abc"), "dopen:0:f:r:wb", "write:0:" + hx(b"zzz"), "error:0", "flush:0:2", "error:0", "close:0")
line("dopen:0:g:w:wb", "write:0:" + hx(b"zzz"), "close:0")
long_name = "n" * 200
line("put:" + long_name + ":" + hx(b"hello"), "open:0:" + long_name + ":rb", "read:0:3", "close:0")
line("put:" + long_name + ":" + hx(b"hello"), "dopen:0:" + long_name + ":r:rb", "close:0")
line("open:0:" + long_name + ":wb", "write:0:" + hx(b"hello"), "close:0", "dump:" + long_name)

# --- 9. NULL and wrong-direction handles
for opn in ["write:0:" + hx(b"ab"), "fwrite:0:1:" + hx(b"ab"), "putc:0:65", "puts:0:" + hx(b"a"), "printf:0:0", "flush:0:2",
            "setparams:0:1:1", "read:0:5", "fread:0:1:5", "gets:0:5", "getc:0", "ungetc:0:65", "seek:0:0:0", "tell:0", "offset:0",
            "rewind:0", "eof:0", "direct:0", "error:0", "clearerr:0", "buffer:0:100", "close:0", "closer:0", "closew:0"]:
    line(opn)                                   # NULL gzFile
    line("open:0:f:wb", opn.replace(":0", ":0", 1), "error:0", "close:0")
    line("put:f:" + hx(gzmember(b"hello gz")), "open:0:f:rb", opn, "error:0", "close:0")
    line("put:f:" + hx(b"raw text"), "open:0:f:rb", opn, "error:0", "close:0")
line("open:0:f:wb", "close:0")
line("open:0:f:wb", "closer:0", "closew:0", "close:0")
line("put:f:" + hx(b"raw text"), "open:0:f:rb", "closew:0")
line("put:f:" + hx(b"raw text"), "open:0:f:rb", "closer:0")

# --- 10. write errors (file size limit), flush kinds, setparams
for lim in [1, 5, 10, 20, 35, 50, 100, 1000]:
    d = rand(300)
    line("fsize:%d" % lim, "open:0:f:wb", "write:0:" + hx(d), "error:0", "flush:0:2", "error:0", "write:0:" + hx(d[:50]), "close:0", "fsize:0", "dump:f")
    line("fsize:%d" % lim, "open:0:f:wbT", "write:0:" + hx(d), "error:0", "write:0:" + hx(d[:10]), "error:0", "close:0", "fsize:0", "dump:f")
    line("fsize:%d" % lim, "open:0:f:wb", "buffer:0:8", *["putc:0:%d" % (65 + i) for i in range(40)], "error:0", "close:0", "fsize:0", "dump:f")
    line("fsize:%d" % lim, "open:0:f:wb", "printf:0:11:s" + (b"p" * 3000).hex(), "error:0", "close:0", "fsize:0", "dump:f")
    line("fsize:%d" % lim, "open:0:f:wb", "write:0:" + hx(d), "close:0", "closew:0", "fsize:0", "open:1:f:rb", "read:1:50", "close:1")
for fl in [-1, 0, 1, 2, 3, 4, 5, 6, 100]:
    line("open:0:f:wb", "write:0:" + hx(text(500)), "flush:0:%d" % fl, "write:0:" + hx(text(100)), "flush:0:%d" % fl, "close:0", "dump:f")
for lv, st in [(1, 0), (9, 0), (0, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (-1, 0), (10, 0), (6, 0), (3, 3)]:
    d = text(3000)
    line("open:0:f:wb", "setparams:0:%d:%d" % (lv, st), "write:0:" + hx(d), "setparams:0:%d:%d" % (lv, st), "setparams:0:5:0", "write:0:" + hx(d[:1000]),
         "close:0", "dump:f", "open:1:f:rb", "read:1:5000", "close:1")
    line("open:0:f:wb", "write:0:" + hx(d), "setparams:0:%d:%d" % (lv, st), "write:0:" + hx(d), "setparams:0:6:0", "error:0", "close:0", "dump:f")
line("open:0:f:wbT", "setparams:0:1:1", "close:0")
line("open:0:f:wb", "write:0:" + hx(text(100)), "setparams:0:6:0", "setparams:0:5:0", "setparams:0:6:0", "close:0", "dump:f")

# --- 11. unget
for pre in ["", "getc:0", "read:0:3", "gets:0:5"]:
    for src in [gzmember(text(1000)), text(1000)]:
        ops = ["put:f:" + hx(src), "open:0:f:rb"] + ([pre] if pre else [])
        line(*ops, "ungetc:0:90", "ungetc:0:91", "getc:0", "getc:0", "getc:0", "read:0:10", "tell:0", "close:0")
        line(*ops, "buffer:0:8" if False else "tell:0", "ungetc:0:-1", "ungetc:0:300", "getc:0", "close:0")
line("put:f:" + hx(text(1000)), "open:0:f:rb", "buffer:0:8", *(["ungetc:0:66"] * 20), "getc:0", "error:0", "close:0")
line("put:f:" + hx(text(1000)), "open:0:f:rb", "buffer:0:8", "read:0:3", *(["ungetc:0:66"] * 20), "getc:0", "error:0", "tell:0", "close:0")
line("put:f:" + hx(gzmember(text(1000))), "open:0:f:rb", "buffer:0:8", "read:0:3", *(["ungetc:0:66"] * 20), "getc:0", "error:0", "tell:0", "close:0")
line("put:f:" + hx(b""), "open:0:f:rb", "ungetc:0:65", "getc:0", "getc:0", "eof:0", "ungetc:0:66", "eof:0", "read:0:5", "close:0")
line("put:f:" + hx(text(50)), "open:0:f:rb", "read:0:100", "eof:0", "ungetc:0:66", "eof:0", "getc:0", "getc:0", "eof:0", "close:0")

# --- 12. eof, error, clearerr
line("put:f:" + hx(text(50)), "open:0:f:rb", "eof:0", "read:0:50", "eof:0", "read:0:1", "eof:0", "clearerr:0", "eof:0", "read:0:1", "eof:0", "close:0")
line("put:f:" + hx(gzmember(text(50))), "open:0:f:rb", "eof:0", "read:0:50", "eof:0", "read:0:1", "eof:0", "clearerr:0", "eof:0", "close:0")
line("open:0:f:wb", "eof:0", "error:0", "clearerr:0", "close:0")

# --- 13. big writes, direct large user buffer paths in gzwrite/gzread
for n in [8191, 8192, 8193, 16384, 16385, 40000]:
    d = text(n)
    line("open:0:f:wb", "write:0:" + hx(d[:100]), "write:0:" + hx(d), "write:0:" + hx(d[:5]), "tell:0", "close:0", "dump:f", "open:1:f:rb",
         "read:1:3", "read:1:%d" % (n + 200), "tell:1", "close:1")
    line("open:0:f:wbT", "write:0:" + hx(d), "close:0", "open:1:f:rb", "read:1:3", "read:1:%d" % (n + 200), "tell:1", "offset:1", "close:1")
    line("open:0:f:wb", "buffer:0:100", "write:0:" + hx(d), "close:0", "open:1:f:rb", "buffer:1:100", "read:1:50", "read:1:%d" % n, "seek:1:10:0", "read:1:%d" % n, "close:1")

# --- 14. interleaving of several handles, reading what was just written
line("open:0:a:wb", "open:1:b:wb", "write:0:" + hx(text(500)), "write:1:" + hx(text(500)), "close:1", "close:0", "dump:a", "dump:b")
line("put:f:" + hx(gzmember(text(500))), "open:0:f:rb", "open:1:f:rb", "read:0:100", "read:1:200", "read:0:100", "close:0", "read:1:300", "close:1")

# --- uncompress2
for n in [0, 1, 10, 100, 1000, 5000, 70000]:
    d = text(n) if n < 5000 else runs(n)
    for lv in (0, 1, 6, 9):
        z = zlib.compress(d, lv)
        out.append("unc %s %d" % (hx(z), n))
        out.append("unc %s %d" % (hx(z), n + 7))
        if n:
            out.append("unc %s %d" % (hx(z), n - 1))
            out.append("unc %s %d" % (hx(z), n // 2))
        out.append("unc %s %d %d" % (hx(z + b"extra"), n, len(z) + 5))
        out.append("unc %s %d %d" % (hx(z + b"extra"), n, len(z)))
        out.append("unc %s %d %d" % (hx(z), n, len(z) - 1))
        out.append("unc %s %d %d" % (hx(z), n, len(z) - 4))
        out.append("unc %s %d" % (hx(z[:len(z) // 2]), n))
    z = zlib.compress(d, 6)
    for pos in sorted(set([0, 1, 2, len(z) // 2, len(z) - 1, len(z) - 3])):
        if 0 <= pos < len(z):
            b = bytearray(z); b[pos] ^= 0x55
            out.append("unc %s %d" % (hx(bytes(b)), n))
out.append("unc - 10")
out.append("unc - 0")
out.append("unc 00 10")
out.append("unc 7801 10")
out.append("unc 789c 0")
out.append("unc 7801030000000001 0")          # empty stored stream (adler 1)
out.append("unc 7801030000000001 5")
out.append("unc 78bb 10")                      # preset dictionary flag set
out.append("unc 78bb0000000000 10")
out.append("unc %s 0" % hx(zlib.compress(b"", 6)))
out.append("unc %s 5" % hx(zlib.compress(b"hello", 6) + b""))
out.append("unc %s 0 %d" % (hx(zlib.compress(b"hello", 6)), 0))

print("\n".join(out))
