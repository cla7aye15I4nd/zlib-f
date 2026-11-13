#!/usr/bin/env python3
"""Check the decoding-side clauses of the inflate format meaning against the real C (driver.c).

For every inflate call the driver prints zlib's internal state. This checker parses the source
with a decoder written from ZlibF/Spec/Format (not from zlib) and lists the parse positions of
the grammar `DeflateParsed` (ZlibF/Proof/inflate.c.meaning.lean) with their bit offsets. A
state in a body mode (TYPE .. LIT) must match one position at the consumed bit count:

  HeldBits, BodyMatches (mode, last, pending token fields, stored length), the proposed
  DynamicMatches (TABLE / LENLENS / CODELENS fields, CODES table contents), bits < 8 at a block
  boundary, WindowMeaning with the proposed `wsize = 0 -> dict ++ out = []`, CheckMeaning,
  and the delivered output.

It also checks the two leave facts of the step lemmas (ZlibF/Proof/inflate.c.meaning-leave-short.lean):

  LeaveShort: a call that returns Z_OK or Z_BUF_ERROR with no input left, and did not stop for a
  Z_BLOCK/Z_TREES flush (TYPE, LEN_, COPY_) or for want of output room (LIT, MATCH, COPY with
  avail_out = 0), holds bits that do not complete the field its mode waits for.
  LoopRefuted: on sessions whose input is the source corrupted after a random point (driver line
  I), a Z_DATA_ERROR call has consumed input that is no beginning of the source and that the
  source does not begin.

This is a test of the statements on finitely many histories, not a proof.
Usage: driver SEED N | check.py. Exits 1 on the first violated clause.
"""
import os
import sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "inflate"))
from check import (Bad, Code, Reader, acceptable, adler32, LBASE, LEXT, DBASE, DEXT,  # noqa: E402
                   CLORDER, FIXED_L, FIXED_D)

TYPE, TYPEDO, STORED, COPY_, COPY, TABLE, LENLENS, CODELENS = range(16191, 16199)
LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT = range(16199, 16206)
BODY = range(TYPE, LIT + 1)
HEAD, DICTID, CHECK, LENGTH = 16180, 16189, 16206, 16207
Z_BLOCK, Z_TREES = 5, 6


def decode_sym(lens, held):
    """decodeSym: the symbol whose canonical code begins `held`, or None."""
    code, c = Code(lens), 0
    for ln in range(1, len(held) + 1):
        c = (c << 1) | held[ln - 1]
        s = code.map.get((ln, c))
        if s is not None:
            return s, ln
    return None


def code_len_extra(sym):
    return {16: 2, 17: 3, 18: 7}.get(sym, 0)


def leave_short(st, held, cl):
    """LeaveShort (ZlibF/Proof/inflate.c.meaning-leave-short.lean) at a starved leave. `cl` is the
    code-length code of the parse position in CODELENS, or None when it is not known."""
    m, n = st["mode"], len(held)
    need = {TYPE: 3, TYPEDO: 3, STORED: 32, TABLE: 14, LENLENS: 3, HEAD: 16, DICTID: 32,
            CHECK: 32, LENGTH: 32}
    if m in (TYPE, TYPEDO) and st["last"]:
        return False
    if m in (HEAD, CHECK) and not st["wrap"]:
        return False
    if m in need:
        return n < need[m]
    if m in (LENEXT, DISTEXT):
        return n < st["extra"]
    if m == COPY:
        return st["length"] != 0
    if m in (LEN, DIST):
        if st["lenfromcodes"]:
            lens = st["lens"][:st["nlen"]] if m == LEN else st["lens"][st["nlen"]:st["nlen"] + st["ndist"]]
        else:
            lens = FIXED_L if m == LEN else FIXED_D
        d = decode_sym(lens, held)
        return d is None or d[0] > (285 if m == LEN else 29)
    if m == CODELENS:
        if cl is None or not any(cl):
            return True
        d = decode_sym(cl, held)
        return d is None or n < d[1] + code_len_extra(d[0])
    return False


def events_of(data, dict_):
    """Parse positions of DeflateParsed, as {bit offset: [event]}, and the decoded output."""
    rd, out, ev = Reader(data), [], {}

    def add(kind, **f):
        ev.setdefault(rd.pos, []).append(dict(kind=kind, out=len(out), **f))

    def symbols(L, D, final):
        lc, dc = Code(L), Code(D)
        while True:
            add("none", final=final)
            s = rd.sym(lc)
            if s < 256:
                add("lit", final=final, byte=s)
                out.append(s)
            elif s == 256:
                return
            else:
                add("lenext", final=final, base=LBASE[s - 257], extra=LEXT[s - 257])
                ln = LBASE[s - 257] + rd.bits(LEXT[s - 257])
                add("dist", final=final, length=ln)
                d = rd.sym(dc)
                add("distext", final=final, length=ln, base=DBASE[d], extra=DEXT[d])
                dist = DBASE[d] + rd.bits(DEXT[d])
                if dist > len(dict_) + len(out):
                    raise Bad("too far")
                add("match", final=final, length=ln, dist=dist)
                for _ in range(ln):
                    j = len(out) - dist
                    out.append(out[j] if j >= 0 else dict_[len(dict_) + j])

    while True:
        add("boundary")
        final = rd.bits(1)
        bt = rd.bits(2)
        if bt == 0:
            add("storedHeader", final=final)
            rd.pos += (-rd.pos) % 8
            add("storedHeader", final=final)  # proposed storedPad: the pad is dropped first
            ln = rd.bits(16)
            if rd.bits(16) != 65535 - ln:
                raise Bad("stored")
            for k in range(ln):
                add("stored", final=final, remaining=ln - k)
                out.append(rd.bits(8))
            add("stored", final=final, remaining=0)
        elif bt == 1:
            symbols(FIXED_L, FIXED_D, final)
        else:
            add("table", final=final)
            hlit, hdist, hclen = rd.bits(5), rd.bits(5), rd.bits(4)
            nlen, ndist, ncode = hlit + 257, hdist + 1, hclen + 4
            cl = [0] * 19
            for i in range(ncode):
                add("lenlens", final=final, nlen=nlen, ndist=ndist, ncode=ncode, have=i,
                    lens=dict((CLORDER[j], cl[CLORDER[j]]) for j in range(i)))
                cl[CLORDER[i]] = rd.bits(3)
            assert acceptable("cl", cl)
            clc, total, lens = Code(cl), nlen + ndist, []
            while len(lens) < total:
                add("codelens", final=final, nlen=nlen, ndist=ndist, ncode=ncode, cl=cl,
                    have=len(lens), lens=list(lens))
                s = rd.sym(clc)
                if s < 16:
                    lens.append(s)
                elif s == 16:
                    lens += [lens[-1]] * (3 + rd.bits(2))
                else:
                    lens += [0] * ((3 + rd.bits(3)) if s == 17 else (11 + rd.bits(7)))
            symbols(lens[:nlen], lens[nlen:], final)
        if final:
            add("finished")
            return ev, out


def code_table(cl, root):
    """The CODES table of a complete code-length code: (op, bits, val) per root index."""
    code, tab = Code(cl), []
    for i in range(1 << root):
        c, ent = 0, None
        for ln in range(1, root + 1):
            c = (c << 1) | ((i >> (ln - 1)) & 1)
            s = code.map.get((ln, c))
            if s is not None:
                ent = (0, ln, s)
                break
        tab.append(ent)
    return tab


def matches(e, st, out_len, bits):
    m, k = st["mode"], e["kind"]
    lastf = lambda: st["last"] == (1 if e.get("final") else 0)  # noqa: E731
    if k in ("boundary", "finished"):
        return (m in (TYPE, TYPEDO) and st["last"] == (1 if k == "finished" else 0)
                and e["out"] == out_len and bits < 8)
    if k == "storedHeader":
        return m == STORED and lastf() and e["out"] == out_len
    if k == "stored":
        return m in (COPY_, COPY) and lastf() and st["length"] == e["remaining"] and e["out"] == out_len
    if k == "table":
        return m == TABLE and lastf()
    if k == "lenlens":
        return (m == LENLENS and lastf() and st["nlen"] == e["nlen"] and st["ndist"] == e["ndist"]
                and st["ncode"] == e["ncode"] and st["have"] == e["have"]
                and all(st["lens"][s] == v for s, v in e["lens"].items()))
    if k == "codelens":
        if not (m == CODELENS and lastf() and st["nlen"] == e["nlen"] and st["ndist"] == e["ndist"]
                and st["ncode"] == e["ncode"] and st["have"] == e["have"]
                and st["lens"][:e["have"]] == e["lens"] and st["lenfromcodes"] == 1):
            return False
        want = code_table(e["cl"], st["lenbits"])
        return all(w is None or w == t for w, t in zip(want, st["table"]))
    if not lastf():
        return False
    if k == "none":
        return m in (LEN_, LEN) and e["out"] == out_len
    if k == "lit":
        return m == LIT and st["length"] == e["byte"] and e["out"] == out_len
    if k == "lenext":
        return m == LENEXT and st["length"] == e["base"] and st["extra"] == e["extra"] and e["out"] == out_len
    if k == "dist":
        return m == DIST and st["length"] == e["length"] and e["out"] == out_len
    if k == "distext":
        return (m == DISTEXT and st["length"] == e["length"] and st["offset"] == e["base"]
                and st["extra"] == e["extra"] and e["out"] == out_len)
    if k == "match":
        written = out_len - e["out"]
        return (m == MATCH and 0 <= written < e["length"] and st["length"] == e["length"] - written
                and st["offset"] == e["dist"])
    return False


FIELDS = ["mode", "last", "length", "offset", "extra", "lenbits", "distbits", "ncode", "nlen",
          "ndist", "have", "wrap", "hold", "bits", "wsize", "whave", "wnext", "wbits", "sane",
          "check", "total", "lenfromcodes", "havedict", "next"]


def parse_state(parts):
    st = {}
    for name, v in zip(FIELDS, parts):
        st[name] = int(v, 16) if name in ("hold", "check") else int(v)
    return st


def bit_at(data, p):
    return (data[p >> 3] >> (p & 7)) & 1


class Fail(Exception):
    pass


def session(lines, stats):
    head = lines[0].split()
    wb, wrap = int(head[1]), int(head[2])
    src = bytes.fromhex(head[3]) if head[3] != "-" else b""
    dict_ = bytes.fromhex(head[4]) if head[4] != "-" else b""
    start = 0
    if wrap:
        start = 16 + (32 if src[1] & 32 else 0)
        log_dict = dict_ if src[1] & 32 else b""
    else:
        log_dict = dict_
    ev, decoded = events_of(src[start // 8:], log_dict)
    outbuf = bytearray()
    corrupted = None
    for ln in lines[1:-1]:
        stats["line"] = ln
        if ln.startswith("I "):
            corrupted = bytes.fromhex(ln.split()[1])
            stats["corrupted"] += 1
            continue
        ln, fpart = ln.split(" F ")
        flush, avail_in, avail_out = (int(x) for x in fpart.split())
        p = ln.split(" W ")
        a = p[0].split()
        ret, tin, tout = int(a[1]), int(a[2]), int(a[3])
        if a[4] != "-":
            outbuf += bytes.fromhex(a[4])
        st = parse_state(a[5:])
        rest, lens_t = p[1].split(" L ")
        window = bytes.fromhex(rest) if rest != "-" else b""
        lens_s, table_s = lens_t.split(" T ")
        st["lens"] = [int(x, 16) for x in lens_s.strip(",").split(",")]
        st["table"] = ([tuple(int(y, 16) for y in x.split(".")) for x in table_s.strip(",").split(",")]
                       if table_s.strip() != "-" else [])
        need = lambda c, what: (_ for _ in ()).throw(Fail(what)) if not c else None  # noqa: E731
        held = [(st["hold"] >> i) & 1 for i in range(st["bits"])]
        m = st["mode"]
        starved = (ret in (0, -5) and avail_in == 0 and
                   not (flush in (Z_BLOCK, Z_TREES) and m in (TYPE, LEN_, COPY_)) and
                   not (avail_out == 0 and m in (LIT, MATCH, COPY)))
        if corrupted is not None:
            if ret == -3:
                read = corrupted[:tin]
                need(not src.startswith(read) and not read.startswith(src),
                     "LoopRefuted: the input read before Z_DATA_ERROR is comparable with the source")
                stats["refuted"] += 1
            if starved and m != CODELENS:
                need(leave_short(st, held, None), "LeaveShort: mode %d holds %d bits" % (m, len(held)))
                stats["short"] += 1
            if ret not in (0, 1, 2, -5, 99):
                break
            continue
        need(ret in (0, 1, 2, -5, 99), "unexpected return %d" % ret)
        need(bytes(outbuf) == bytes(decoded[:len(outbuf)]), "output is not the decoded prefix")
        need(st["hold"] < (1 << st["bits"]), "hold above bits")
        if st["mode"] not in BODY:
            if starved and st["mode"] in (HEAD, DICTID, CHECK, LENGTH):
                need(leave_short(st, held, None), "LeaveShort: mode %d holds %d bits" % (m, len(held)))
                stats["short"] += 1
            stats["other"] += 1
            continue
        n = 8 * tin - st["bits"] - start
        heldv = sum(bit_at(src, start + n + i) << i for i in range(st["bits"]))
        need(heldv == st["hold"], "HeldBits: hold is not the next input bits")
        cand = ev.get(n, [])
        fits = [e for e in cand if matches(e, st, len(outbuf), st["bits"])]
        need(fits, "BodyMatches: no parse position at bit %d fits mode %d (candidates %s)"
             % (n, st["mode"], [e["kind"] for e in cand]))
        if starved:
            cl = next((e["cl"] for e in fits if e["kind"] == "codelens"), None)
            need(leave_short(st, held, cl), "LeaveShort: mode %d holds %d bits" % (m, len(held)))
            stats["short"] += 1
        hist = log_dict + bytes(outbuf)
        if st["wsize"]:
            need(window == hist[len(hist) - min(len(hist), st["wsize"]):], "WindowMeaning content")
        else:
            need(st["whave"] == 0 and hist == b"", "WindowMeaning: no window with history")
        need(st["total"] == len(outbuf), "CheckMeaning total")
        if st["wrap"] & 4:
            need(st["check"] == adler32(bytes(outbuf)), "CheckMeaning check")
        stats["body"] += 1
        stats[st["mode"]] = stats.get(st["mode"], 0) + 1
    stats["sessions"] += 1


def main():
    stats = {"sessions": 0, "body": 0, "other": 0, "corrupted": 0, "refuted": 0, "short": 0}
    block = []
    for line in sys.stdin:
        line = line.rstrip("\n")
        block.append(line)
        if line == "E":
            try:
                session(block, stats)
            except Fail as e:
                print("VIOLATED:", e)
                print(block[0][:300])
                print(stats["line"][:300])
                sys.exit(1)
            block = []
    names = {TYPE: "TYPE", TYPEDO: "TYPEDO", STORED: "STORED", COPY_: "COPY_", COPY: "COPY",
             TABLE: "TABLE", LENLENS: "LENLENS", CODELENS: "CODELENS", LEN_: "LEN_", LEN: "LEN",
             LENEXT: "LENEXT", DIST: "DIST", DISTEXT: "DISTEXT", MATCH: "MATCH", LIT: "LIT"}
    print("ok: %d sessions (%d corrupted), %d body states, %d other, %d starved leaves, "
          "%d data errors refuted; by mode: %s" % (
        stats["sessions"], stats["corrupted"], stats["body"], stats["other"], stats["short"],
        stats["refuted"],
        ", ".join("%s %d" % (names[m], stats[m]) for m in sorted(names) if m in stats)))


if __name__ == "__main__":
    main()
