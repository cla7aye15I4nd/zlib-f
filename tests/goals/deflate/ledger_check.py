#!/usr/bin/env python3
"""Check the deflate ledger claims against records of the real C (ledger.c).

At every call boundary, E = bits(delivered ++ pending) ++ held bits (LSB first). The claims:
  L1  emitted = header ++ blocks: in a header state E is a prefix of the wrapper header bits
      (with deflatePrime bits); in BUSY/FINISH, E = header ++ complete blocks ++ tail, no final
      block before FINISH_STATE, and after the final block only zero padding and the trailer
      (once wrap < 0).
  L2  the complete blocks decode (history: dictionaries, reset at a full flush, distance at most
      2^windowBits) to inp[0..k).
  L3  level > 0: replaying the recorded symbols from k reproduces inp[k..k+r), and
      k + r + match_available + lookahead = accepted; level 0: window[block_start..strstart] =
      inp[k..k+span) and k + span + lookahead = accepted.
  L4  window[0..strstart+lookahead] is the suffix of the history (dictionaries and input in order).
  L5  after Z_STREAM_END: everything delivered, the stream decodes to the input, trailer correct.
The decoder follows the format specification (check.py), not zlib. Evidence, not proof.

Usage: ledger_check.py < records
       ledger_check.py --run LEDGER_BINARY SESSIONS SEED JOBS
"""
import binascii
import os
import subprocess
import sys
from multiprocessing import Pool

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import check as C  # noqa: E402  format tables, Acceptable, checksums

HEADER_STATES = {42, 57, 69, 73, 91, 103}
BUSY, FINISH = 113, 666


class OutOfBits(Exception):
    pass


class Bad(Exception):
    pass


class Bits:
    def __init__(self, data, n):
        self.d = bytes(data) + b"\0" * 8
        self.n = n

    def get(self, pos, k):
        if pos + k > self.n:
            raise OutOfBits()
        b = pos >> 3
        return (int.from_bytes(self.d[b:b + 4], "little") >> (pos & 7)) & ((1 << k) - 1)


def rev(c, ln):
    r = 0
    for _ in range(ln):
        r = (r << 1) | (c & 1)
        c >>= 1
    return r


def table(lens):
    mx = max(lens) if lens else 0
    if mx == 0:
        return (0, None)
    bl = [0] * 16
    for x in lens:
        if x:
            bl[x] += 1
    code, nxt = 0, [0] * 16
    for b in range(1, 16):
        code = (code + bl[b - 1]) << 1
        nxt[b] = code
    t = [-1] * (1 << mx)
    for s, x in enumerate(lens):
        if x:
            r = rev(nxt[x], x)
            nxt[x] += 1
            for i in range(r, 1 << mx, 1 << x):
                t[i] = (s << 4) | x
    return (mx, t)


FIXED = (table(C.FIXED_L), table(C.FIXED_D))


def dsym(bits, pos, tb):
    mx, t = tb
    if t is None:
        raise Bad("symbol from an empty code")
    b = pos >> 3
    v = (int.from_bytes(bits.d[b:b + 4], "little") >> (pos & 7)) & ((1 << mx) - 1)
    e = t[v]
    if e < 0:
        if pos + mx > bits.n:
            raise OutOfBits()
        raise Bad("invalid code")
    ln = e & 15
    if pos + ln > bits.n:
        raise OutOfBits()
    return e >> 4, pos + ln


def block(bits, pos, hist, wsize):
    """One block from bit pos; appends its output to hist. Returns (final, new pos)."""
    final = bits.get(pos, 1)
    bt = bits.get(pos + 1, 2)
    pos += 3
    if bt == 0:
        pos += (-pos) % 8
        ln = bits.get(pos, 16)
        nln = bits.get(pos + 16, 16)
        pos += 32
        if nln != 65535 - ln:
            raise Bad("stored NLEN")
        if pos + 8 * ln > bits.n:
            raise OutOfBits()
        hist += bits.d[pos >> 3:(pos >> 3) + ln]
        return final, pos + 8 * ln
    if bt == 1:
        lt, dt = FIXED
    elif bt == 2:
        hlit, hdist, hclen = bits.get(pos, 5), bits.get(pos + 5, 5), bits.get(pos + 10, 4)
        pos += 14
        if hlit + 257 > 286 or hdist + 1 > 30:
            raise Bad("too many symbols")
        cl = [0] * 19
        for i in range(hclen + 4):
            cl[C.CLORDER[i]] = bits.get(pos, 3)
            pos += 3
        if not C.acceptable("cl", cl):
            raise Bad("code length code")
        ct = table(cl)
        total, lens = hlit + 257 + hdist + 1, []
        while len(lens) < total:
            s, pos = dsym(bits, pos, ct)
            if s < 16:
                lens.append(s)
            elif s == 16:
                if not lens:
                    raise Bad("repeat without previous")
                r = 3 + bits.get(pos, 2)
                pos += 2
                if len(lens) + r > total:
                    raise Bad("repeat overrun")
                lens += [lens[-1]] * r
            else:
                k = 3 if s == 17 else 7
                r = (3 if s == 17 else 11) + bits.get(pos, k)
                pos += k
                if len(lens) + r > total:
                    raise Bad("repeat overrun")
                lens += [0] * r
        L, D = lens[:hlit + 257], lens[hlit + 257:]
        if L[256] == 0:
            raise Bad("missing end of block")
        if not C.acceptable("ll", L) or not C.acceptable("d", D):
            raise Bad("bad code lengths")
        lt, dt = table(L), table(D)
    else:
        raise Bad("block type 3")
    LB, LE, DB, DE = C.LBASE, C.LEXT, C.DBASE, C.DEXT
    while True:
        s, pos = dsym(bits, pos, lt)
        if s < 256:
            hist.append(s)
        elif s == 256:
            return final, pos
        elif s <= 285:
            ln = LB[s - 257] + bits.get(pos, LE[s - 257])
            pos += LE[s - 257]
            d, pos = dsym(bits, pos, dt)
            if d > 29:
                raise Bad("distance symbol 30/31")
            dist = DB[d] + bits.get(pos, DE[d])
            pos += DE[d]
            if dist > len(hist):
                raise Bad("distance %d before the history (%d)" % (dist, len(hist)))
            if dist > wsize:
                raise Bad("distance %d beyond the window %d" % (dist, wsize))
            for _ in range(ln):
                hist.append(hist[-dist])
        else:
            raise Bad("literal/length symbol 286/287")


def be32(x):
    return bytes([(x >> 24) & 255, (x >> 16) & 255, (x >> 8) & 255, x & 255])


def le32(x):
    return (x & 0xFFFFFFFF).to_bytes(4, "little")


def tobits(bs):
    out = []
    for b in bs:
        out += [(b >> i) & 1 for i in range(8)]
    return out


class Session:
    def __init__(self, S, report):
        _, seed, wrap, wb, mem, lvl, strat, osc, wsize = S.split()
        self.seed, self.wrap, self.wb, self.mem = int(seed), int(wrap), int(wb), int(mem)
        self.level0, self.strat0, self.oscode, self.wsize = int(lvl), int(strat), int(osc), int(wsize)
        self.report = report
        self.gz = None
        self.inp, self.Hc, self.hcidx = bytearray(), bytearray(), []
        self.dictcat, self.events, self.ev = bytearray(), [], 0
        self.prime = []
        self.E = bytearray()
        self.syms = bytearray()
        self.step = 0
        self.ops = []
        self.hdr = None              # (level, strategy) when the header was written
        self.last = (self.level0, self.strat0)
        self.started = False
        self.barrier_hc = 0
        self.dec_pos, self.dec_out, self.dec_hist = None, 0, bytearray()
        self.final, self.broken = False, False
        self.rp = None
        self.prime_wrap = False
        self.hyp = None
        self.trailer_cache = None
        self.done = False

    def fail(self, claim, msg):
        self.report(claim, self, msg)

    # ------------------------------------------------------------ the header model
    def header(self):
        lv, st = self.hdr if self.hdr else self.last
        if self.wrap == 0:
            return b""
        dc = self.hdr_dict if self.hdr else self.dictcat
        if self.wrap == 1:
            lf = 0 if (st >= 2 or lv < 2) else 1 if lv < 6 else 2 if lv == 6 else 3
            h = ((8 + ((self.wb - 8) << 4)) << 8) | (lf << 6) | (0x20 if dc else 0)
            h += 31 - h % 31
            out = bytes([h >> 8, h & 255])
            if dc:
                out += be32(C.adler32_update(1, bytes(dc)))
            return out
        xfl = 2 if lv == 9 else (4 if (st >= 2 or lv < 2) else 0)
        if self.gz is None:
            return bytes([31, 139, 8, 0, 0, 0, 0, 0, xfl, self.oscode])
        text, time, os_, hcrc, extra, name, comment = self.gz
        fl = (1 if text else 0) + (2 if hcrc else 0) + (4 if extra is not None else 0) + \
             (8 if name is not None else 0) + (16 if comment is not None else 0)
        h = bytes([31, 139, 8, fl]) + le32(time) + bytes([xfl, os_ & 255])
        if extra is not None:
            h += bytes([len(extra) & 255, (len(extra) >> 8) & 255]) + extra
        if name is not None:
            h += name + b"\0"
        if comment is not None:
            h += comment + b"\0"
        if hcrc:
            c = C.crc32_update(0, h)
            h += bytes([c & 255, (c >> 8) & 255])
        return h

    def prefixes(self):
        hb = tobits(self.header())
        pb = self.prime
        t = 8 * (len(pb) // 8)
        A = hb + pb
        B = pb[:t] + hb + pb[t:]
        return A, B

    # ------------------------------------------------------------ records
    def line(self, f):
        k = f[0]
        if k == "H":
            rc = int(f[1])
            if rc == 0:
                def g(x):
                    return None if x == "-" else b"" if x == "x-" else bytes.fromhex(x[1:])
                self.gz = (int(f[2]), int(f[3]), int(f[4]), int(f[5]), g(f[6]), g(f[7]), g(f[8]))
        elif k == "I":
            if f[1] != "-":
                b = bytes.fromhex(f[1])
                base = len(self.Hc)
                self.hcidx.extend(range(base, base + len(b)))
                self.Hc += b
                self.inp += b
        elif k == "D":
            self.ops.append("D%s:%d" % (f[1], len(f[2]) // 2))
            if int(f[1]) == 0:
                if self.wrap and self.started:
                    self.stats["dictionary accepted after the start with a wrapper (wrap<0 after trailer)"] += 1
                d = bytes.fromhex(f[2])
                self.Hc += d[-self.wsize:]      # deflateSetDictionary keeps the last w_size bytes
                self.dictcat += d
                self.events.append((len(self.inp), "dict", d))
        elif k == "P":
            self.ops.append("P%s:%s" % (f[1], f[2]))
            if int(f[1]) == 0:
                bits, val = int(f[2]), int(f[3])
                self.prime += [(val >> i) & 1 for i in range(bits)]
                if self.wrap and bits:
                    self.prime_wrap = True
        elif k == "NM":
            self.fail("E-monotone", " ".join(f))
        elif k == "W":
            pass
        elif k == "R":
            self.boundary(f)

    def boundary(self, f):
        (op, flush, rc, status, wrap_s, level, strategy, strstart, lookahead, block_start, ma,
         insert, bi_valid, bibuf, tout, pending, sn, given, taken, wcrc, wl, bc, sf) = \
            [f[1]] + [int(x) for x in f[2:24]]
        symhex, symcrc, ehex = f[24], int(f[25]), f[26]
        self.step += 1
        if op == "d":
            self.ops.append("d%d:%d/%d:%d" % (flush, taken, given, rc))
            self.started = True
        elif op == "p":
            self.ops.append("p%d.%d:%d" % (flush // 10, flush % 10, rc))
        elif op == "t":
            self.ops.append("t")
        self.cur = dict(level=level, strategy=strategy, strstart=strstart, lookahead=lookahead,
                        block_start=block_start, ma=ma, status=status)
        # the header is written by the call that leaves INIT_STATE or GZIP_STATE, with the level,
        # strategy and dictionaries of the boundary before it
        if self.hdr is None and status not in (42, 57):
            self.hdr = self.last
            self.hdr_dict = bytes(self.dictcat)
        self.last = (level, strategy)
        old_elen = len(self.E)
        if ehex != "-":
            self.E += bytes.fromhex(ehex)
        # the symbol buffer
        self.syms = self.syms[:sf] + (bytes.fromhex(symhex) if symhex != "-" else b"")
        if len(self.syms) != sn or (binascii.crc32(self.syms) & 0xFFFFFFFF) != symcrc:
            self.fail("harness", "symbol buffer reconstruction")
        # full flush barrier
        if op == "d" and flush == 3 and given == taken and bi_valid == 0 and \
                len(self.E) - old_elen >= 4 and self.E[-4:] == b"\0\0\xff\xff":
            self.events.append((len(self.inp), "barrier", None))
            self.barrier_hc = len(self.Hc)
            self.stats["barrier"] += 1
        accepted = len(self.inp)
        # ---------------- L4 window
        if wl > len(self.Hc) or (binascii.crc32(self.Hc[len(self.Hc) - wl:]) & 0xFFFFFFFF) != wcrc:
            self.fail("L4", "window[0..%d] is not the suffix of the history (len %d)" % (wl, len(self.Hc)))
        # ---------------- L1 prefix
        nE = 8 * len(self.E) + bi_valid
        data = bytes(self.E) + bytes([bibuf])
        A, B = self.prefixes()
        plen = len(A)
        ebits = int.from_bytes(data[:(plen + 7) // 8 + 1], "little")

        def match(P):
            m = min(len(P), nE)
            return all(((ebits >> i) & 1) == P[i] for i in range(m))
        okA, okB = match(A), match(B)
        if status in HEADER_STATES:
            if nE > plen:
                self.fail("L1-header", "E has %d bits beyond the %d header bits in status %d" % (nE - plen, plen, status))
            elif not okA:
                # the measured relation with deflatePrime: the prime bits flushed to bytes come
                # first, the header bytes follow, the rest of the prime bits stay held
                pb = self.prime
                t = 8 * (len(pb) // 8)
                want = bytes(int("".join(map(str, reversed(pb[j:j + 8]))), 2) for j in range(0, t, 8)) + self.header()
                rest = pb[t:]
                if bytes(self.E) == want[:len(self.E)] and bi_valid == len(rest) and \
                        all(((bibuf >> j) & 1) == rest[j] for j in range(len(rest))):
                    self.stats["header phase with prime: E = primebytes ++ header prefix, held = prime rest"] += 1
                else:
                    self.fail("L1-header", "E is not a prefix of the header in status %d" % status)
            return self.l3(level, strstart, lookahead, block_start, ma, sn, bc, accepted, header=True)
        if status not in (BUSY, FINISH):
            self.fail("L1", "unexpected status %d" % status)
            return
        if nE < plen or not (okA or okB):
            if not self.broken:
                self.fail("L1-prefix" + ("-primewrap" if self.prime_wrap else ""),
                          "E (%d bits) does not start with header++prime (%d bits) in status %d" % (nE, plen, status))
            self.broken = True
            return
        hyp = "A" if okA else "B"
        if self.hyp is None and plen:
            self.hyp = hyp
            if self.prime_wrap:
                self.stats["prime+wrapper: header then prime (A)" if okA else "prime+wrapper: prime bytes, header, prime rest (B)"] += 1
        if self.dec_pos is None:
            self.dec_pos = plen
        # ---------------- L2: decode complete blocks
        if not self.broken and not self.final:
            bits = Bits(data, nE)
            while True:
                while self.ev < len(self.events) and self.events[self.ev][0] <= self.dec_out:
                    pos_, kind, d = self.events[self.ev]
                    if pos_ < self.dec_out:
                        self.fail("L2-event", "%s event at input %d inside a block ending at %d" % (kind, pos_, self.dec_out))
                    if kind == "dict":
                        self.dec_hist += d
                    else:
                        self.dec_hist = bytearray()
                    self.ev += 1
                h0 = len(self.dec_hist)
                try:
                    fin, np = block(bits, self.dec_pos, self.dec_hist, 1 << self.wb)
                except OutOfBits:
                    del self.dec_hist[h0:]
                    break
                except Bad as e:
                    self.fail("L2", "block at bit %d: %s" % (self.dec_pos, e))
                    self.broken = True
                    break
                got = bytes(self.dec_hist[h0:])
                if self.inp[self.dec_out:self.dec_out + len(got)] != got:
                    self.fail("L2", "block at bit %d decodes to %d bytes not equal to input[%d..] (accepted %d)" %
                              (self.dec_pos, len(got), self.dec_out, accepted))
                    self.broken = True
                    break
                self.dec_out += len(got)
                self.dec_pos = np
                self.stats["blocks"] += 1
                if len(self.dec_hist) > 4 * self.wsize + 70000:
                    del self.dec_hist[:len(self.dec_hist) - 2 * self.wsize]
                if fin:
                    self.final = True
                    if status != FINISH:
                        self.fail("L1-final", "final block while status %d" % status)
                    break
        if self.broken:
            return
        # ---------------- L1 tail
        if not self.final:
            left = nE - self.dec_pos
            self.stats["tail bits %s" % (left if left < 8 else ">=8")] += 1
            if left >= 8:
                self.fail("L1-tail", "%d bits after the complete blocks (held %d, pending %d)" % (left, bi_valid, pending))
            elif left > 0:
                self.stats["tail bits nonzero, flush %d op %s" % (flush, op)] += 1
        else:
            al = self.dec_pos + (-self.dec_pos) % 8
            pad_ok = all(((data[i >> 3] >> (i & 7)) & 1) == 0 for i in range(self.dec_pos, min(al, nE)))
            rest = self.E[al // 8:] if al <= 8 * len(self.E) else b""
            if not pad_ok:
                self.fail("L1-trailer", "nonzero padding after the final block")
            if bi_valid and al < nE:
                self.fail("L1-trailer", "held bits after the final block's byte boundary")
            if wrap_s < 0:
                if self.trailer_cache is None or self.trailer_cache[0] != accepted:
                    if self.wrap == 1:
                        t = be32(C.adler32_update(1, bytes(self.inp)))
                    else:
                        t = le32(C.crc32_update(0, bytes(self.inp))) + le32(accepted)
                    self.trailer_cache = (accepted, t)
                if bytes(rest) != self.trailer_cache[1]:
                    self.fail("L1-trailer", "bytes after the final block are not the trailer")
            elif rest:
                self.fail("L1-trailer", "%d bytes after the final block before the trailer phase (wrap %d)" % (len(rest), wrap_s))
        # ---------------- L5
        if op == "d" and rc == 1:
            self.stats["finished"] += 1
            self.stats["finished %s%s" % (["raw", "zlib", "gzip"][self.wrap],
                                          " with header record" if self.gz else "")] += 1
            if not self.final or self.dec_out != accepted:
                self.fail("L5", "finished but decoded %d of %d (final %s)" % (self.dec_out, accepted, self.final))
            if pending or bi_valid or tout != len(self.E):
                self.fail("L5", "finished with pending %d held %d" % (pending, bi_valid))
            if self.wrap and wrap_s >= 0:
                self.fail("L5", "finished without the trailer phase")
            if self.barrier_hc:
                self.stats["finished with full flush"] += 1
            if [e for e in self.events if e[1] == "dict" and e[0] > 0]:
                self.stats["finished with raw dictionary mid-stream"] += 1
            self.done = True
        self.l3(level, strstart, lookahead, block_start, ma, sn, bc, accepted)

    # ------------------------------------------------------------ L3 open block
    def l3(self, level, strstart, lookahead, block_start, ma, sn, bc, accepted, header=False):
        k = self.dec_out
        span = strstart - block_start
        if level == 0:
            if sn:
                self.stats["level 0 with recorded symbols"] += 1
            if k + span + lookahead != accepted:
                self.fail("L3-0", "k %d + span %d + lookahead %d != accepted %d (ma %d)" % (k, span, lookahead, accepted, ma))
            elif bc >= 0 and (binascii.crc32(self.inp[k:k + span]) & 0xFFFFFFFF) != bc:
                self.fail("L3-0", "window[block_start..strstart] != input[k..k+span]")
            elif bc < 0:
                self.stats["level 0 with block_start < 0"] += 1
            else:
                self.stats["L3-0 checked"] += 1
            return
        rp = self.rp
        if rp is None or rp[0] != k or 3 * rp[1] > len(self.syms) or rp[3] != self.syms[:3 * rp[1]]:
            rp = [k, 0, k, b"", True]
        if rp[4]:
            i, n = rp[2], rp[1]
            maxd = self.wsize - 262
            while 3 * n < len(self.syms):
                d = self.syms[3 * n] | (self.syms[3 * n + 1] << 8)
                lc = self.syms[3 * n + 2]
                ok = True
                if d == 0:
                    if i >= accepted or self.inp[i] != lc:
                        self.fail("L3", "literal %d at input %d does not match (accepted %d)" % (lc, i, accepted))
                        ok = False
                    else:
                        i += 1
                else:
                    ln = lc + 3
                    if d > maxd:
                        self.fail("L3-dist", "recorded distance %d > MAX_DIST %d" % (d, maxd))
                    for _ in range(ln):
                        if i >= accepted:
                            self.fail("L3", "match runs past the accepted input")
                            ok = False
                            break
                        h = self.hcidx[i]
                        src = h - d
                        if i > k and self.hcidx[i - 1] != h - 1:
                            self.fail("L3", "a dictionary sits inside the open block")
                            ok = False
                            break
                        if self.hcidx[k] >= self.barrier_hc > src:
                            self.fail("L3-barrier", "match reaches before a full flush")
                        if src < 0 or self.Hc[src] != self.inp[i]:
                            self.fail("L3", "match (len %d, dist %d) at input %d does not reproduce the input" % (ln, d, i))
                            ok = False
                            break
                        i += 1
                if not ok:
                    rp[4] = False
                    break
                n += 1
            rp[1], rp[2] = n, i
            rp[3] = bytes(self.syms[:3 * n])
        self.rp = rp
        if not rp[4]:
            return
        r = rp[2] - k
        if ma:
            self.stats["L3 boundaries with match_available=1"] += 1
        if block_start < 0:
            self.stats["L3 boundaries with block_start < 0 (slid)"] += 1
        if r > 0 and not header:
            self.stats["L3 boundaries with a nonempty open block"] += 1
        d1 = k + r + ma + lookahead - accepted
        d2 = span - (r + ma)
        self.stats["L3 k+r+ma+la-acc=%d" % d1] += 1
        self.stats["L3 span-(r+ma)=%d" % d2] += 1
        if d1 != 0:
            self.fail("L3", "k %d + replay %d + ma %d + lookahead %d - accepted %d = %d; span %d" %
                      (k, r, ma, lookahead, accepted, d1, span))
        if d2 != 0:
            self.fail("L3-span", "strstart-block_start %d != replay %d + ma %d (k %d accepted %d)" % (span, r, ma, k, accepted))


class Stats(dict):
    def __missing__(self, k):
        return 0


def check_stream(lines_iter):
    fails = {}
    stats = Stats()

    def report(claim, s, msg):
        key = (claim, msg.split(" ")[0] if claim.startswith("L3") else claim)
        size = len(s.inp) + 50 * s.step
        ent = fails.get(claim)
        if ent is None:
            fails[claim] = [1, set([s.seed]), (size, s.seed, s.step, msg, s.desc(), " ".join(s.ops))]
        else:
            ent[0] += 1
            ent[1].add(s.seed)
            if size < ent[2][0]:
                ent[2] = (size, s.seed, s.step, msg, s.desc(), " ".join(s.ops))

    sess = None
    for line in lines_iter:
        f = line.split()
        if not f:
            continue
        if f[0] == "S":
            if len(f) < 9:
                continue
            sess = Session(line, report)
            sess.stats = stats
            stats["sessions"] += 1
        elif f[0] == "X":
            if sess is not None:
                if sess.prime_wrap:
                    stats["sessions with prime and a wrapper"] += 1
            sess = None
        elif sess is not None and not sess.done:
            sess.line(f)
    return fails, dict(stats)


def desc(self):
    return "wrap %s wb %d mem %d level %d strat %d gzhdr %s dict %d prime %d" % (
        ["raw", "zlib", "gzip"][self.wrap], self.wb, self.mem, self.level0, self.strat0,
        "yes" if self.gz else "no", len(self.dictcat), len(self.prime))


Session.desc = desc


def run_job(args):
    binary, count, seed = args
    p = subprocess.Popen([binary, str(count), str(seed)], stdout=subprocess.PIPE, text=True, bufsize=1 << 20)
    res = check_stream(p.stdout)
    p.wait()
    return res


def merge(results):
    fails, stats = {}, Stats()
    for fl, st in results:
        for k, v in st.items():
            stats[k] += v
        for c, (n, seeds, ex) in fl.items():
            if c not in fails:
                fails[c] = [0, set(), ex]
            fails[c][0] += n
            fails[c][1] |= seeds
            if ex[0] < fails[c][2][0]:
                fails[c][2] = ex
    return fails, stats


def main():
    if len(sys.argv) > 1 and sys.argv[1] == "--run":
        binary, n, seed, jobs = sys.argv[2], int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5])
        chunk = 250
        tasks = [(binary, min(chunk, seed + n - s), s) for s in range(seed, seed + n, chunk)]
        with Pool(jobs) as pool:
            fails, stats = merge(pool.imap_unordered(run_job, tasks))
    else:
        fails, stats = merge([check_stream(sys.stdin)])
    for k in sorted(stats):
        print("stat  %-60s %d" % (k, stats[k]))
    claims = ["E-monotone", "harness", "L1-header", "L1", "L1-prefix", "L1-prefix-primewrap", "L1-final",
              "L1-tail", "L1-trailer", "L2", "L2-event", "L3", "L3-span", "L3-dist", "L3-0", "L4", "L5"]
    for c in claims + sorted(set(fails) - set(claims)):
        if c in fails:
            n, seeds, ex = fails[c]
            print("FAIL  %-20s %d failures in %d sessions" % (c, n, len(seeds)))
            print("      smallest: seed %d step %d: %s" % (ex[1], ex[2], ex[3]))
            print("      %s" % ex[4])
            print("      history: %s" % ex[5][:600])
        else:
            print("PASS  %s" % c)
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
