#!/usr/bin/env python3
"""Check the clauses of the deflate goals against records of the real C (driver.c).

The decoder below is written from the format specification (ZlibF/Spec/Format/Deflate.lean,
Huffman.lean, Wrapper.lean), not from zlib: it accepts exactly the derivations of Blocks, Body,
Symbols and CodeLens, with Acceptable code lengths. The checksums are computed here as well.
This is a test of the statements on finitely many histories, not a proof.

Usage: check.py < records. Exits 1 on the first violated clause and prints the session.
"""
import sys

Z_NO_FLUSH, Z_PARTIAL_FLUSH, Z_SYNC_FLUSH, Z_FULL_FLUSH, Z_FINISH, Z_BLOCK, Z_TREES = 0, 1, 2, 3, 4, 5, 6
Z_OK, Z_STREAM_END, Z_STREAM_ERROR, Z_BUF_ERROR = 0, 1, -2, -5
INIT_STATE, BUSY_STATE, FINISH_STATE = 42, 113, 666

# ---------------------------------------------------------------- checksums (Spec/Format/Checksum)

def adler32_update(a, data):
    s1, s2 = a & 0xFFFF, a >> 16
    for i in range(0, len(data), 3800):
        for b in data[i:i + 3800]:
            s1 += b
            s2 += s1
        s1 %= 65521
        s2 %= 65521
    return (s2 << 16) | s1

_CRC = []
for n in range(256):
    c = n
    for _ in range(8):
        c = (0xEDB88320 ^ (c >> 1)) if c & 1 else c >> 1
    _CRC.append(c)

def crc32_update(c, data):
    c ^= 0xFFFFFFFF
    for b in data:
        c = _CRC[(c ^ b) & 0xFF] ^ (c >> 8)
    return c ^ 0xFFFFFFFF

# ---------------------------------------------------------------- the format (Spec/Format/Deflate)

class Bad(Exception):
    pass

LBASE = [3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31, 35, 43, 51, 59, 67, 83, 99, 115,
         131, 163, 195, 227, 258]
LEXT = [0] * 8 + [1] * 4 + [2] * 4 + [3] * 4 + [4] * 4 + [5] * 4 + [0]
DBASE = [1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193, 257, 385, 513, 769, 1025, 1537,
         2049, 3073, 4097, 6145, 8193, 12289, 16385, 24577]
DEXT = [0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12, 13, 13]
CLORDER = [16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15]
FIXED_L = [8] * 144 + [9] * 112 + [7] * 24 + [8] * 8
FIXED_D = [5] * 32


def acceptable(kind, lens):
    """Huffman.Acceptable: lengths at most 15, not over-subscribed, and complete, or empty, or
    (not for the code-length code) a single symbol of length 1."""
    if any(x > 15 for x in lens):
        return False
    kraft = sum(2 ** (15 - x) for x in lens if x)
    if kraft > 2 ** 15:
        return False
    if kraft == 2 ** 15:
        return True
    nz = [x for x in lens if x]
    if not nz:
        return True
    return kind != "cl" and nz == [1]


class Code:
    """Canonical code: decodeSym finds the symbol whose code is a prefix of the input."""
    def __init__(self, lens):
        self.map = {}
        bl_count = [0] * 16
        for x in lens:
            if x:
                bl_count[x] += 1
        code, nxt = 0, [0] * 16
        for b in range(1, 16):
            code = (code + bl_count[b - 1]) << 1
            nxt[b] = code
        for s, x in enumerate(lens):
            if x:
                self.map[(x, nxt[x])] = s
                nxt[x] += 1


class Reader:
    def __init__(self, data, pos=0):
        self.data, self.pos, self.n = data, pos, 8 * len(data)

    def bits(self, k):
        if self.pos + k > self.n:
            raise Bad("out of bits")
        v = 0
        for i in range(k):
            p = self.pos + i
            v |= ((self.data[p >> 3] >> (p & 7)) & 1) << i
        self.pos += k
        return v

    def sym(self, code):
        c = 0
        for ln in range(1, 16):
            if self.pos >= self.n:
                raise Bad("out of bits")
            p = self.pos
            c = (c << 1) | ((self.data[p >> 3] >> (p & 7)) & 1)
            self.pos += 1
            s = code.map.get((ln, c))
            if s is not None:
                return s
        raise Bad("invalid code")


def symbols(rd, L, D, dict_, out, barrier):
    """Symbols: decode until end of block. barrier: no copy may reach before out position
    barrier (None: no restriction); returns the smallest position a copy reached."""
    lc, dc = Code(L), Code(D)
    while True:
        s = rd.sym(lc)
        if s < 256:
            out.append(s)
        elif s == 256:
            return
        elif s <= 285:
            ln = LBASE[s - 257] + rd.bits(LEXT[s - 257])
            d = rd.sym(dc)
            if d > 29:
                raise Bad("distance symbol 30/31")
            dist = DBASE[d] + rd.bits(DEXT[d])
            if dist > len(dict_) + len(out):
                raise Bad("distance too far")
            if barrier is not None and len(out) - dist < barrier:
                raise Bad("copy reaches before a full flush point")
            for _ in range(ln):
                j = len(out) - dist
                out.append(out[j] if j >= 0 else dict_[len(dict_) + j])
        else:
            raise Bad("literal/length symbol 286/287")


def block(rd, dict_, out, barrier):
    """One block: BFINAL, BTYPE, Body. Returns BFINAL."""
    final = rd.bits(1)
    bt = rd.bits(2)
    if bt == 0:
        rd.pos += (-rd.pos) % 8     # inp.drop (inp.length % 8): the rest of the byte
        ln = rd.bits(16)
        nln = rd.bits(16)
        if nln != 65535 - ln:
            raise Bad("stored NLEN")
        for _ in range(ln):
            out.append(rd.bits(8))
    elif bt == 1:
        symbols(rd, FIXED_L, FIXED_D, dict_, out, barrier)
    elif bt == 2:
        hlit, hdist, hclen = rd.bits(5), rd.bits(5), rd.bits(4)
        if hlit + 257 > 286 or hdist + 1 > 30:
            raise Bad("too many symbols")
        cl = [0] * 19
        for i in range(hclen + 4):
            cl[CLORDER[i]] = rd.bits(3)
        if not acceptable("cl", cl):
            raise Bad("code length code")
        clc = Code(cl)
        total, lens = hlit + 257 + hdist + 1, []
        while len(lens) < total:
            s = rd.sym(clc)
            if s < 16:
                lens.append(s)
            elif s == 16:
                if not lens:
                    raise Bad("repeat without previous")
                r = 3 + rd.bits(2)
                if len(lens) + r > total:
                    raise Bad("repeat overrun")
                lens += [lens[-1]] * r
            else:
                r = (3 + rd.bits(3)) if s == 17 else (11 + rd.bits(7))
                if len(lens) + r > total:
                    raise Bad("repeat overrun")
                lens += [0] * r
        L, D = lens[:hlit + 257], lens[hlit + 257:]
        if L[256] == 0:
            raise Bad("missing end of block")
        if not acceptable("ll", L) or not acceptable("d", D):
            raise Bad("bad code lengths")
        symbols(rd, L, D, dict_, out, barrier)
    else:
        raise Bad("block type 3")
    return final


def deflate_prefix(data, dict_, barriers=()):
    """Deflate.Prefix dict stream tail out: returns (out, tail). barriers: list of
    (bit position, out position) of full flush points: a block that starts at or after such a bit
    position may not copy from before that out position."""
    rd, out = Reader(data), []
    while True:
        bar = None
        for bp, op in barriers:
            if rd.pos >= bp:
                bar = op
        if block(rd, dict_, out, bar):
            break
    rd.pos += (-rd.pos) % 8
    return bytes(out), data[rd.pos // 8:]


def deflate_open(data, dict_):
    """Non-final blocks that use exactly all bits of data (a completed sync or full flush)."""
    rd, out = Reader(data), []
    while rd.pos < rd.n:
        if block(rd, dict_, out, None):
            raise Bad("final block before a flush point")
    if rd.pos != rd.n:
        raise Bad("flush point not at the end of the bits")
    return bytes(out)


def be32(x):
    return bytes([(x >> 24) & 255, (x >> 16) & 255, (x >> 8) & 255, x & 255])


def le32(x):
    return bytes([x & 255, (x >> 8) & 255, (x >> 16) & 255, (x >> 24) & 255])


def split_wrapper(wrap, wbits, dict_, stream):
    """The wrapper of Zlib.Decodes / Gzip.Decodes; returns (deflate part, dictionary for it,
    function checking the trailer)."""
    if wrap == "raw":
        return stream, dict_[len(dict_) - min(len(dict_), 2 ** wbits):], None
    if wrap == "zlib":
        if len(stream) < 2:
            raise Bad("short zlib header")
        cmf, flg = stream[0], stream[1]
        if cmf % 16 != 8 or cmf // 16 > 7 or (cmf * 256 + flg) % 31:
            raise Bad("zlib header")
        if flg // 32 % 2:
            if stream[2:6] != be32(adler32_update(1, dict_)):
                raise Bad("DICTID")
            ws = 2 ** (cmf // 16 + 8)
            return stream[6:], dict_[len(dict_) - min(len(dict_), ws):], "zlib"
        return stream[2:], b"", "zlib"
    # gzip, header as deflate writes it without a gz_header: no flags
    if len(stream) < 10 or stream[:4] != bytes([31, 139, 8, 0]):
        raise Bad("gzip header")
    return stream[10:], b"", "gzip"


def decodes_for(wrap, wbits, dict_, stream, barriers):
    body, d, kind = split_wrapper(wrap, wbits, dict_, stream)
    off = len(stream) - len(body)
    out, tail = deflate_prefix(body, d, [(8 * (b - off), o) for b, o in barriers])
    if kind is None:
        want = b""
    elif kind == "zlib":
        want = be32(adler32_update(1, out))
    else:
        want = le32(crc32_update(0, out)) + le32(len(out) % 2 ** 32)
    if tail != want:
        raise Bad("trailer or trailing bytes")
    return out


def flush_point(wrap, wbits, dict_, stream):
    body, d, _ = split_wrapper(wrap, wbits, dict_, stream)
    return deflate_open(body, d)

# ---------------------------------------------------------------- the model bound (Api.DeflState.bound)

def model_bound(p, dict_eff, n):
    level, wrap, wbits, mem = p["level"], p["wrap"], p["wbits"], p["mem"]
    fixedlen = n + n // 8 + n // 256 + n // 512 + 4
    storelen = n + n // 32 + n // 128 + n // 2048 + 7
    wraplen = {"raw": 0, "zlib": 6 + (4 if dict_eff else 0), "gzip": 18}[wrap]
    if wbits != 15 or mem + 7 != 15:
        b = (fixedlen if wbits <= mem + 7 and level != 0 else storelen) + wraplen
    else:
        b = n + n // 4096 + n // 16384 + n // 2 ** 25 + 13 - 6 + wraplen
    return min(b, 2 ** 64 - 1)


def deflinit(level, method, wb, mem, strategy):
    """Api.deflInit?"""
    lv = 6 if level == -1 else level
    if wb < 0:
        if wb < -15:
            return None
        wr, w = "raw", -wb
    elif wb > 15:
        wr, w = "gzip", wb - 16
    else:
        wr, w = "zlib", wb
    if mem < 1 or mem > 9 or method != 8 or w < 8 or w > 15 or lv < 0 or lv > 9 or strategy < 0 \
            or strategy > 4 or (w == 8 and wr != "zlib"):
        return None
    return {"level": lv, "wrap": wr, "wbits": 9 if w == 8 else w, "mem": mem, "strategy": strategy}


def rank(f):
    return f * 2 - (9 if f > 4 else 0)

# ---------------------------------------------------------------- the clauses

stats = {}


def count(k):
    stats[k] = stats.get(k, 0) + 1


def check_session(lines):
    S = lines[0].split()
    level, method, wb, mem, strategy, rc = map(int, S[1:7])
    p = deflinit(level, method, wb, mem, strategy)
    if (p is None) != (rc != Z_OK):
        raise Bad("deflateInit2_ result against Api.deflInit?")
    if p is None:
        return
    count("sessions")
    dictionary = b""
    inp = b""
    log_in, log_out = bytearray(), bytearray()
    finished, eligible = False, True
    barriers = []
    for ln in lines[1:]:
        f = ln.split()
        if f[0] == "D":
            r = int(f[1])
            d = b"" if f[2] == "-" else bytes.fromhex(f[2])
            if r == Z_OK:
                dictionary += d
            if (r == Z_OK) != (p["wrap"] != "gzip"):
                raise Bad("deflateSetDictionary result")
        elif f[0] == "B":
            n, b, bz = int(f[1]), int(f[2]), int(f[3])
            m = model_bound(p, dictionary, n)
            if b != m or bz != m:
                raise Bad("deflateBound before data %d %d, model %d" % (b, bz, m))
            count("bound agrees")
        elif f[0] == "I":
            inp = b"" if f[1] == "-" else bytes.fromhex(f[1])
        elif f[0] == "C":
            check_call(p, f, dictionary, inp, log_in, log_out, barriers, finished, eligible)
            flush, rcv = int(f[1]), int(f[f.index("->") + 1])
            eligible = eligible and flush == Z_FINISH
            finished = finished or rcv == Z_STREAM_END
            if finished and rcv == Z_STREAM_END and not getattr(check_session, "_ended", False):
                pass
        elif f[0] == "E":
            pass


def check_call(p, f, dictionary, inp, log_in, log_out, barriers, finished, eligible):
    a = f.index("->")
    flush, nullin, nullout = int(f[1]), int(f[2]), int(f[3])
    ain, aout, status, pending, bi_valid, last, wrap, lookahead, strstart = map(int, f[4:13])
    tin, tout, adler, dtype, msg = int(f[13]), int(f[14]), int(f[15]), int(f[16]), f[17]
    rc, ain2, aout2, status2, pending2, bi2, wrap2, adler2, dtype2 = map(int, f[a + 1:a + 10])
    msg2, tin2, tout2 = f[a + 10], int(f[a + 11]), int(f[a + 12])
    out = b"" if (a + 13 >= len(f) or f[a + 13] == "-") else bytes.fromhex(f[a + 13])
    used, produced = ain - ain2, aout - aout2
    count("calls")
    # Goal.deflate: accounting
    if used < 0 or produced < 0 or (not nullout and len(out) != produced):
        raise Bad("accounting")
    if nullin and used:
        raise Bad("used from a NULL input")
    if tin2 != (tin + used) % 2 ** 64 or tout2 != (tout + produced) % 2 ** 64:
        raise Bad("totals")
    if rc not in (Z_OK, Z_STREAM_END, Z_STREAM_ERROR, Z_BUF_ERROR):
        raise Bad("result code")
    serr = flush < 0 or flush > 5 or nullout or (nullin and ain != 0) or (status == FINISH_STATE and flush != Z_FINISH)
    if (rc == Z_STREAM_ERROR) != serr:
        raise Bad("STREAM_ERROR iff")
    if (flush < 0 or flush > 5) and (used or produced or msg2 != msg or status2 != status):
        raise Bad("invalid flush changes the heap")
    if rc == Z_STREAM_END and not (flush == Z_FINISH and status2 == FINISH_STATE and ain2 == 0 and pending2 == 0 and bi2 == 0):
        raise Bad("STREAM_END facts")
    # new: Z_BUF_ERROR means no progress, except draining the pending trailer of a finished stream
    if rc == Z_BUF_ERROR:
        count("buf_error")
        if used != 0 or not (produced == 0 or (status == FINISH_STATE and ain != 0)):
            raise Bad("BUF_ERROR with progress")
        if produced:
            count("buf_error after drain")
    if not serr and aout == 0 and not (rc == Z_BUF_ERROR and used == 0 and produced == 0):
        raise Bad("avail_out = 0 must give BUF_ERROR without progress")
    possible = (ain != 0 or pending != 0 or flush == Z_FINISH or rank(last) < rank(flush))
    if not serr and aout != 0 and not (status == FINISH_STATE and ain != 0) and possible and rc == Z_BUF_ERROR:
        raise Bad("BUF_ERROR although progress was possible")
    if not serr and aout != 0 and not (status == FINISH_STATE and ain != 0) and not possible and rc != Z_BUF_ERROR:
        raise Bad("no BUF_ERROR although no progress was possible")
    if flush == Z_FINISH and not serr and aout != 0 and not (status == FINISH_STATE and ain != 0):
        count("finish progress")
        if not (rc == Z_STREAM_END or used or produced):
            raise Bad("FINISH call without progress")
    # msg and data_type
    if rc in (Z_OK, Z_STREAM_END) and msg2 != msg:
        raise Bad("msg changed on success")
    if rc == Z_BUF_ERROR and msg2 != "buffer":
        raise Bad("msg on BUF_ERROR")
    if rc == Z_STREAM_ERROR and not (flush < 0 or flush > 5) and msg2 != "stream":
        raise Bad("msg on STREAM_ERROR")
    if not (dtype2 == dtype or (dtype == 2 and dtype2 in (0, 1))):
        raise Bad("data_type")
    # the log
    if not nullin:
        log_in += inp[len(log_in):len(log_in) + used]
    log_out += out
    # adler after a successful call
    if rc in (Z_OK, Z_STREAM_END) and p["wrap"] != "raw":
        want = adler32_update(1, bytes(log_in)) if p["wrap"] == "zlib" else crc32_update(0, bytes(log_in))
        if adler2 != want:
            raise Bad("adler after a successful call")
        count("adler")
    # DeflateCompletes
    if eligible and not finished and flush == Z_FINISH and not nullout and aout > 0 and not nullin \
            and (status != FINISH_STATE or ain == 0) \
            and model_bound(p, dictionary, len(log_in) - used + ain) <= len(log_out) - produced + aout:
        count("completes")
        if rc != Z_STREAM_END:
            raise Bad("DeflateCompletes: FINISH with bound room did not end")
    # flush points
    if flush in (Z_SYNC_FLUSH, Z_FULL_FLUSH) and rc == Z_OK and aout2 != 0 and not finished:
        count("flush point")
        if ain2 != 0:
            raise Bad("flush point with unconsumed input")
        got = flush_point(p["wrap"], p["wbits"], dictionary, bytes(log_out))
        if got != bytes(log_in):
            raise Bad("flush point does not decode to the input so far")
        if flush == Z_FULL_FLUSH:
            barriers.append((len(log_out), len(log_in)))
    if rc == Z_STREAM_END and not finished:
        count("finished")
        got = decodes_for(p["wrap"], p["wbits"], dictionary, bytes(log_out), barriers)
        if got != bytes(log_in):
            raise Bad("finished output does not decode to the accepted input")
        if barriers:
            count("finished with full flush")


def main():
    session = []
    def run(sess):
        if not sess:
            return
        try:
            check_session(sess)
        except Bad as e:
            print("VIOLATION: %s" % e)
            for x in sess:
                print(x[:300])
            sys.exit(1)
    for line in sys.stdin:
        line = line.rstrip("\n")
        if line.startswith("S "):
            run(session)
            session = []
        if line:
            session.append(line)
    run(session)
    for k in sorted(stats):
        print("%s %d" % (k, stats[k]))


if __name__ == "__main__":
    main()
