#!/usr/bin/env python3
"""Inputs for the infback.c differential test, written to stdout.

Deterministic: fixed seed, no clock, no environment. One line per case (format: tests/c/infback.c):
  infback WB INCH OPTS hex:INPUT
The inputs are raw deflate streams made with Python's zlib module, then corrupted, truncated, followed by trailing bytes
and fed in pieces of many sizes; the windows are smaller than, equal to and larger than the one the stream was made with.
"""
import random
import zlib

rng = random.Random(20261105)
out = []

def case(wb, inch, opts, data):
    out.append("infback %d %d %d hex:%s" % (wb, inch, opts, bytes(data).hex()))

WORDS = [b"the ", b"quick ", b"brown ", b"fox ", b"jumps ", b"over ", b"lazy ", b"dog ", b"zlib ", b"\n"]
def text(n):
    b = bytearray()
    while len(b) < n:
        b += rng.choice(WORDS)
    return bytes(b[:n])
def randbytes(n):
    return bytes(rng.randrange(256) for _ in range(n))
def longrange(n):
    blk = randbytes(300)
    gap = randbytes(900)
    return (blk + gap + blk + gap[:100] + blk)[:n]

def raw(data, level=6, wbits=15, strategy=0):
    c = zlib.compressobj(level, zlib.DEFLATED, -wbits, 8, strategy)
    return c.compress(data) + c.flush()

streams = []
for nm, d in (("text", text(1500)), ("rand", randbytes(900)), ("long", longrange(1800)), ("zero", bytes(1200)),
              ("small", text(40)), ("empty", b""), ("one", b"x"), ("big", text(9000))):
    for lvl in (0, 1, 6, 9):
        streams.append((nm + "-l%d" % lvl, raw(d, lvl)))
    streams.append((nm + "-fixed", raw(d, 6, 15, 4)))
    streams.append((nm + "-huff", raw(d, 6, 15, 2)))
    streams.append((nm + "-rle", raw(d, 6, 15, 3)))
    streams.append((nm + "-w9", raw(d, 9, 9)))
    streams.append((nm + "-w12", raw(d, 9, 12)))

for nm, st in streams:
    for wb in (15, 12, 9, 8):
        for inch in (1, 7, 100, 100000):
            case(wb, inch, 0, st)
    case(15, 3, 1, st)
    case(15, 3, 2, st)
    case(15, 1000, 4, st)
    case(9, 5, 5, st)
    case(15, 1000, 1, st)
    case(15, 1000, 2, st)

# invalid window sizes and corrupted streams
base = [raw(text(600), 6), raw(longrange(1800), 9), raw(randbytes(300), 0), raw(text(300), 6, 15, 4)]
for wb in (7, 16, 0, -1, 8, 15):
    case(wb, 10, 0, base[0])
hows = []
for st in base:
    n = len(st)
    case(15, 1, 0, st + b"trailing")
    case(15, 1000, 0, st + b"trailing bytes after the end")
    case(15, 1000, 4, st + b"trailing bytes after the end")
    for cut in (0, 1, 2, 3, n // 3, n // 2, n - 2, n - 1):
        case(15, 7, 0, st[:max(cut, 0)])
        case(15, 1000, 0, st[:max(cut, 0)])
    for i in (0, 1, 2, 3, 4, 5, 8, 12, 20, 33, 50, 70, 100, 150):
        s = bytearray(st)
        s[i % n] ^= 1 << (i % 8)
        case(15, 1000, 0, bytes(s))
        case(15, 3, 0, bytes(s))
        case(9, 16, 0, bytes(s))
for t in range(80):
    s = bytearray(base[t % len(base)])
    for _ in range(1 + t % 3):
        s[rng.randrange(len(s))] = rng.randrange(256)
    case(rng.choice((15, 12, 9, 8)), rng.choice((1, 5, 64, 1000)), rng.choice((0, 0, 1, 4)), bytes(s))
for t in range(60):
    g = bytes([rng.choice((0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x0d, 0xed, 0xfd, 0xe5))]) + randbytes(rng.randrange(0, 60))
    case(rng.choice((15, 9, 8)), rng.choice((1, 6, 1000)), rng.choice((0, 4)), g)

# hand-made blocks: stored with bad complement, an invalid dynamic header, an empty last block
case(15, 1, 0, bytes([1, 5, 0, 0, 0]) + b"hello")
case(15, 1, 0, bytes([1, 5, 0, 0xfa, 0xff]) + b"hello")
case(15, 2, 0, bytes([0, 5, 0, 0xfa, 0xff]) + b"hello" + bytes([1, 0, 0, 0xff, 0xff]))
case(15, 2, 1, bytes([0, 5, 0, 0xfa, 0xff]) + b"hello" + bytes([1, 0, 0, 0xff, 0xff]))
case(15, 2, 2, bytes([0, 5, 0, 0xfa, 0xff]) + b"hello" + bytes([1, 0, 0, 0xff, 0xff]))
case(15, 2, 0, bytes([0, 200, 0, 0x37, 0xff]) + randbytes(200) + bytes([1, 0, 0, 0xff, 0xff]))
case(8, 2, 0, bytes([0, 255, 1, 0x00, 0xfe]) + randbytes(511) + bytes([1, 0, 0, 0xff, 0xff]))
case(8, 300, 1, bytes([0, 255, 1, 0x00, 0xfe]) + randbytes(511) + bytes([1, 0, 0, 0xff, 0xff]))

# Isolate the HLIT boundary without another malformed field masking its refusal.
# BFINAL=1, BTYPE=dynamic, HDIST=1 and HCLEN=4; no code-length payload follows.
# In particular 287 must fail at the count check, before requesting more input.
for nlen in (286, 287, 288):
    header = bytes([5 | ((nlen - 257) << 3), 0, 0])
    for chunk in (1, 1000):
        case(15, chunk, 0, header)

for line in out:
    print(line)
