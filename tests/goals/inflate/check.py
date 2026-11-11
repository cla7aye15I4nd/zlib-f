#!/usr/bin/env python3
"""Check the clauses of the inflate goals against records of the real C (driver.c).

The decoder below is written from the format specification (ZlibF/Spec/Format/Deflate.lean,
Huffman.lean, Wrapper.lean) and the API layer (ZlibF/Spec/Api/Basic.lean, InflateAccepted.lean),
not from zlib. This is a test of the statements on finitely many histories, not a proof.

Usage: check.py < records. Exits 1 on the first violated clause and prints the session.
"""
import sys

Z_NO_FLUSH, Z_SYNC_FLUSH, Z_FINISH, Z_BLOCK, Z_TREES = 0, 2, 4, 5, 6
Z_OK, Z_STREAM_END, Z_NEED_DICT = 0, 1, 2
Z_STREAM_ERROR, Z_DATA_ERROR, Z_MEM_ERROR, Z_BUF_ERROR = -2, -3, -4, -5
DICT, DONE, BAD, MEM, SYNC = 16190, 16208, 16209, 16210, 16211

# ---------------------------------------------------------------- checksums (Spec/Format/Checksum)

def adler32(data):
    s1, s2 = 1, 0
    for b in data:
        s1 = (s1 + b) % 65521
        s2 = (s2 + s1) % 65521
    return (s2 << 16) | s1

_CRC = []
for _n in range(256):
    _c = _n
    for _ in range(8):
        _c = (0xEDB88320 ^ (_c >> 1)) if _c & 1 else _c >> 1
    _CRC.append(_c)

def crc32(data):
    c = 0xFFFFFFFF
    for b in data:
        c = _CRC[(c ^ b) & 0xFF] ^ (c >> 8)
    return c ^ 0xFFFFFFFF

# ---------------------------------------------------------------- deflate (Spec/Format/Deflate)

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
    def __init__(self, data):
        self.data, self.pos, self.n = data, 0, 8 * len(data)

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


def symbols(rd, L, D, dict_, out):
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
            for _ in range(ln):
                j = len(out) - dist
                out.append(out[j] if j >= 0 else dict_[len(dict_) + j])
        else:
            raise Bad("literal/length symbol 286/287")


def block(rd, dict_, out):
    final = rd.bits(1)
    bt = rd.bits(2)
    if bt == 0:
        rd.pos += (-rd.pos) % 8
        ln = rd.bits(16)
        nln = rd.bits(16)
        if nln != 65535 - ln:
            raise Bad("stored NLEN")
        for _ in range(ln):
            out.append(rd.bits(8))
    elif bt == 1:
        symbols(rd, FIXED_L, FIXED_D, dict_, out)
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
        symbols(rd, L, D, dict_, out)
    else:
        raise Bad("block type 3")
    return final


def deflate_prefix(data, dict_):
    """Deflate.Prefix dict stream tail out: returns (out, tail)."""
    rd, out = Reader(data), []
    while not block(rd, dict_, out):
        pass
    rd.pos += (-rd.pos) % 8
    return bytes(out), data[rd.pos // 8:]


def be32(x):
    return bytes([(x >> 24) & 255, (x >> 16) & 255, (x >> 8) & 255, x & 255])


def le32(x):
    return bytes([x & 255, (x >> 8) & 255, (x >> 16) & 255, (x >> 24) & 255])


def tail_dict(d, n):
    return d[len(d) - min(len(d), n):]

# ---------------------------------------------------------------- wrappers (Spec/Format/Wrapper)

def raw_decodes(dict_, stream):
    out, tail = deflate_prefix(stream, dict_)
    if tail:
        raise Bad("bytes after the raw stream")
    return out


def zlib_decodes_window(window, dict_, stream):
    """Zlib.DecodesWithWindow window (window 0: the header's window, which is Zlib.Decodes)."""
    if len(stream) < 2:
        raise Bad("short zlib header")
    cmf, flg = stream[0], stream[1]
    if cmf % 16 != 8 or cmf // 16 > 7 or (cmf * 256 + flg) % 31:
        raise Bad("zlib header")
    body, d = stream[2:], b""
    if flg // 32 % 2:
        if stream[2:6] != be32(adler32(dict_)):
            raise Bad("DICTID")
        body = stream[6:]
        d = tail_dict(dict_, 2 ** (cmf // 16 + 8) if window == 0 else 2 ** window)
    out, tail = deflate_prefix(body, d)
    if tail != be32(adler32(out)):
        raise Bad("zlib trailer")
    return out


def gzip_decodes(stream):
    if len(stream) < 10 or stream[0] != 31 or stream[1] != 139 or stream[2] != 8:
        raise Bad("gzip header")
    flg = stream[3]
    if flg >= 32:
        raise Bad("gzip reserved flags")
    p = 10
    if flg & 4:
        if p + 2 > len(stream):
            raise Bad("short XLEN")
        xlen = stream[p] | (stream[p + 1] << 8)
        p += 2 + xlen
    for bit in (8, 16):
        if flg & bit:
            z = stream.find(b"\0", p)
            if z < 0:
                raise Bad("unterminated string")
            p = z + 1
    if p > len(stream):
        raise Bad("short header")
    if flg & 2:
        if stream[p:p + 2] != (crc32(stream[:p]) & 0xffff).to_bytes(2, "little"):
            raise Bad("header CRC")
        p += 2
    out, tail = deflate_prefix(stream[p:], b"")
    if tail != le32(crc32(out)) + le32(len(out) % 2 ** 32):
        raise Bad("gzip trailer")
    return out


def zlib_fits(wbits, stream):
    return wbits == 0 or (len(stream) > 0 and stream[0] // 16 + 8 <= wbits)


def attempt(f, *a):
    try:
        return f(*a)
    except (Bad, IndexError):
        return None

# ---------------------------------------------------------------- API layer (Spec/Api)

def infl_wbits(w):
    """Api.inflWbits."""
    if w < 0:
        if w < -15 or -w < 8:
            return None
        return ("raw", -w)
    q = w // 16
    wrap = {0: "zlib", 1: "gzip", 2: "auto"}.get(q)
    if wrap is None:
        return None
    wb = w % 16 if w < 48 else w
    if wb != 0 and (wb < 8 or wb > 15):
        return None
    return (wrap, wb)


def layer_decodes(wrap, bits, dict_, stream):
    """Api.Layer.Decodes: the decoding or None."""
    if wrap == "raw":
        return attempt(raw_decodes, tail_dict(dict_, 2 ** bits), stream)
    z = attempt(zlib_decodes_window, 0, dict_, stream) if zlib_fits(bits, stream) else None
    if wrap == "zlib":
        return z
    g = attempt(gzip_decodes, stream)
    if wrap == "gzip":
        return g
    return z if z is not None else g


def inflate_accepted(wrap, bits, dict_, stream, out):
    """Api.Layer.InflateAccepted wrap bits dict stream out."""
    if wrap == "raw":
        return attempt(raw_decodes, tail_dict(dict_, 2 ** bits), stream) == out
    z = zlib_fits(bits, stream) and attempt(zlib_decodes_window, bits, dict_, stream) == out
    if wrap == "zlib":
        return z
    g = attempt(gzip_decodes, stream) == out
    return g if wrap == "gzip" else (z or g)


def full_window(wrap, bits, stream):
    """Api.FullWindow."""
    if wrap == "raw":
        return bits == 15
    if wrap == "gzip":
        return bits in (0, 15)
    head15 = len(stream) == 0 or stream[0] // 16 + 8 == 15
    if wrap == "zlib":
        return bits == 15 or (bits == 0 and head15)
    return bits == 15 or (bits == 0 and (stream[:1] == b"\x1f" or head15))

# ---------------------------------------------------------------- checks

class Fail(Exception):
    pass


def need(cond, what):
    if not cond:
        raise Fail(what)


def h(x):
    return b"" if x == "-" else bytes.fromhex(x)


def check_call(f, log):
    """Goal.inflate on one call. f: the parsed C record."""
    used, made = f["ain"] - f["ain2"], f["aout"] - f["aout2"]
    out, rc, flush = f["out"], f["rc"], f["flush"]
    need(rc in (Z_OK, Z_STREAM_END, Z_NEED_DICT, Z_STREAM_ERROR, Z_DATA_ERROR, Z_MEM_ERROR,
                Z_BUF_ERROR), "result code")
    need(0 <= used <= f["ain"] and 0 <= made <= f["aout"], "accounting bounds")
    need(f["nullout"] or len(out) == made, "written bytes")
    if f["nullout"]:
        need(made == 0, "no output through a null pointer")
    progress = used != 0 or made != 0
    if rc == Z_OK:
        need(progress and flush != Z_FINISH, "Z_OK means progress and not Z_FINISH")
    refuse = f["nullout"] or (f["nullin"] and f["ain"] != 0) or f["mode"] == SYNC
    need((rc == Z_STREAM_ERROR) == bool(refuse), "Z_STREAM_ERROR iff refusal")
    if rc == Z_STREAM_ERROR:
        need(f["same"] and used == 0 and made == 0, "refusal changes nothing")
    if rc == Z_BUF_ERROR:
        need(not progress or flush == Z_FINISH, "Z_BUF_ERROR without progress or under Z_FINISH")
    if f["ain"] and f["aout"] and flush not in (Z_BLOCK, Z_TREES) and rc == Z_BUF_ERROR:
        need(progress, "progress with input and output space")
    if rc == Z_STREAM_END:
        need(f["mode2"] == DONE, "Z_STREAM_END in DONE")
    if rc == Z_NEED_DICT:
        need(f["mode2"] == DICT, "Z_NEED_DICT in DICT")
    if rc == Z_DATA_ERROR:
        need(f["mode2"] == BAD, "Z_DATA_ERROR in BAD")
    if rc == Z_MEM_ERROR:
        need(f["mode2"] == MEM and f["tin2"] == f["tin"] and f["tout2"] == f["tout"], "Z_MEM_ERROR")
    if rc in (Z_OK, Z_STREAM_END, Z_DATA_ERROR, Z_BUF_ERROR):
        need(f["tin2"] == (f["tin"] + used) % 2 ** 64 and f["tout2"] == (f["tout"] + made) % 2 ** 64,
             "totals")
    need(f["nullin"] or f["consumed"] is not None, "consumed bytes")


_cache = {}


def decoding(cfg, dict_, source):
    key = (cfg, bytes(dict_), source)
    if key not in _cache:
        if len(_cache) > 64:
            _cache.clear()
        _cache[key] = layer_decodes(cfg[0], cfg[1], bytes(dict_), source)
    return _cache[key]


def check_format(cfg, log, source):
    """The two data clauses of Goal.inflate_sequence on the current protocol log."""
    wrap, bits = cfg
    decoded = decoding(cfg, log["dict"], source)
    if log["single"] and log["result"] == Z_STREAM_END:
        need(inflate_accepted(wrap, bits, log["dict"], bytes(log["input"]), bytes(log["output"])),
             "a finished epoch consumed an accepted stream")
    if decoded is None or not log["single"] or not full_window(wrap, bits, source):
        return
    inp, outp = bytes(log["input"]), bytes(log["output"])
    if not source.startswith(inp):
        return
    need(decoded.startswith(outp), "output is a prefix of the decoding")
    need(log["result"] != Z_DATA_ERROR, "no data error on a valid stream")
    if log["result"] == Z_STREAM_END:
        need(inp == source and outp == decoded, "the end is exactly the stream end")


def check_completes(cfg, log, source, f):
    """InflateCompletes on a probe call."""
    wrap, bits = cfg
    decoded = decoding(cfg, log["dict"], source)
    if decoded is None or not log["single"] or log["finished"] or not full_window(wrap, bits, source):
        return
    inp = bytes(log["input"])
    if not source.startswith(inp) or f["nullin"] or f["nullout"]:
        return
    if f["consumed_all"] != source[len(inp):]:
        return
    if f["mode"] in (BAD, MEM, SYNC) or (f["mode"] == DICT and f["havedict"] == 0):
        return
    if len(decoded) > len(log["output"]) + f["aout"]:
        return
    if f["flush"] not in (Z_NO_FLUSH, Z_SYNC_FLUSH, Z_FINISH):
        return
    rc = f["rc"]
    if rc == Z_STREAM_END:
        need(bytes(log["output"]) + f["out"] == decoded, "completion delivers the rest")
        return
    if rc == Z_NEED_DICT:
        need(f["havedict"] == 0 and wrap in ("zlib", "auto") and len(source) >= 2 and
             source[1] // 32 % 2 == 1 and f["mode2"] == DICT and f["aout2"] == f["aout"],
             "completion asks for a missing zlib dictionary")
        return
    raise Fail("completion: rc %d" % rc)


def parse_call(parts):
    a = parts.index("->")
    probe, flush, nullin, nullout, ain, aout, mode, havedict, tin, tout = map(int, parts[1:a])
    rc, ain2, aout2, mode2, tin2, tout2, same = map(int, parts[a + 1:a + 8])
    return dict(probe=probe, flush=flush, nullin=nullin, nullout=nullout, ain=ain, aout=aout,
                mode=mode, havedict=havedict, tin=tin, tout=tout, rc=rc, ain2=ain2, aout2=aout2,
                mode2=mode2, tin2=tin2, tout2=tout2, same=same, consumed=h(parts[a + 8]),
                out=h(parts[a + 9]))


def check_session(lines):
    stats = {"calls": 0, "accepted": 0, "prefix": 0, "probes": 0}
    first = lines[0].split()
    wb, rc = int(first[1]), int(first[2])
    cfg = infl_wbits(wb)
    # the state is allocated before windowBits is checked, so a failed allocation comes first
    need(rc == Z_MEM_ERROR or (rc == Z_OK) == (cfg is not None), "init accepts exactly inflWbits")
    if rc != Z_OK:
        return stats
    protocol = int(lines[1].split()[1]) == 1
    failing = int(lines[1].split()[2]) == 1
    g = lines[2].split()
    source = h(g[4])
    log = dict(input=bytearray(), output=bytearray(), dict=b"", result=Z_OK, single=True,
               finished=False)
    pending = False
    for line in lines[5:]:
        parts = line.split()
        if parts[0] == "C":
            f = parse_call(parts)
            stats["calls"] += 1
            check_call(f, log)
            if protocol and f["probe"]:
                stats["probes"] += 1
                pres = source[len(log["input"]):]
                f["consumed_all"] = pres if f["ain"] == len(pres) else None
                if not failing:
                    check_completes(cfg, log, source, f)
            used = f["ain"] - f["ain2"]
            if not f["nullin"]:
                need(len(f["consumed"]) == used, "consumed length")
                log["input"] += f["consumed"]
            if not f["nullout"]:
                log["output"] += f["out"]
            log["result"] = f["rc"]
            log["finished"] = log["finished"] or f["rc"] == Z_STREAM_END
            pending = f["rc"] == Z_NEED_DICT
        elif parts[0] == "D":
            r, d = int(parts[1]), h(parts[2])
            raw = cfg[0] == "raw"
            if not (raw or r != Z_OK or pending):
                protocol = False
            if r == Z_OK:
                if raw and (log["input"] or log["output"]):
                    log["single"] = False
                log["dict"] = log["dict"] + d if raw else d
            if not raw:
                pending = pending if r != Z_OK else False
        elif parts[0] == "Q":
            protocol = False
        if protocol and parts[0] in ("C", "D"):
            check_format(cfg, log, source)
            if log["single"] and log["result"] == Z_STREAM_END:
                stats["accepted"] += 1
            elif decoding(cfg, log["dict"], source) is not None:
                stats["prefix"] += 1
    return stats


def main():
    total = {"sessions": 0, "calls": 0, "accepted": 0, "prefix": 0, "probes": 0}
    session = []

    def run(s):
        try:
            st = check_session(s)
        except Fail as e:
            print("VIOLATED:", e)
            print("\n".join(x[:400] for x in s))
            sys.exit(1)
        total["sessions"] += 1
        for k, v in st.items():
            total[k] += v

    for line in sys.stdin:
        line = line.rstrip("\n")
        if line.startswith("S ") and session:
            run(session)
            session = []
        if line:
            session.append(line)
    if session:
        run(session)
    print("ok:", " ".join("%s=%d" % kv for kv in total.items()))


if __name__ == "__main__":
    main()
