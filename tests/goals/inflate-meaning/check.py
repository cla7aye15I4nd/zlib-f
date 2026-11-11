#!/usr/bin/env python3
"""State-level test of ParseMeaning, stream side (ZlibF/Proof/inflate.c.meaning*.lean).

Reads the records of driver.c (protocol sessions, with a `T` line of private decoder fields after
every call) and checks, on every prefix of a valid source in the configured layer, the facts that
the stream-side stages of the format meaning claim about the real decoder:

* configuration: `wrap` is the code of the configured layer (0, 5, 6, 7), no header record, `sane`,
  a nonzero configured width is the decoder width;
* header modes: a wrapped header has no dictionary and no window yet; the consumed bits are whole
  header bytes; with FHCRC the gzip check is the CRC-32
  of the header bytes consumed; the gzip flags word once read; `DICTID` after the 2 zlib bytes, with `FDICT` set;
* header modes and `DICT`: `last` and `total` are 0;
* `DICT`: after 6 bytes, `check` is the DICTID, `havedict = 0` exactly while a request is pending,
  and then no window yet;
* block modes: the consumed bits lie in the body; `flags` is -1 (raw), 0 (zlib) or the gzip word;
  at a block boundary fewer than 8 bits are held; `total` and `check` are the length and checksum
  of the output;
* `CHECK` at the byte-aligned end of the body, `LENGTH` 4 bytes later (gzip only);
* `DONE`: nothing held, the whole source consumed.

The consumed bits are 8 * (input bytes taken) - `bits`. The parse of the source is computed from
the format specification (tests/goals/inflate/check.py), not from zlib. Evidence on finitely many
histories, not a proof.
"""
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "inflate"))
import check as F  # noqa: E402

MODES = ("HEAD FLAGS TIME OS EXLEN EXTRA NAME COMMENT HCRC DICTID DICT TYPE TYPEDO STORED COPY_ "
         "COPY TABLE LENLENS CODELENS LEN_ LEN LENEXT DIST DISTEXT MATCH LIT CHECK LENGTH DONE BAD "
         "MEM SYNC").split()
M = {name: 16180 + i for i, name in enumerate(MODES)}
NAME = {v: k for k, v in M.items()}
WRAPCODE = {"raw": 0, "zlib": 5, "gzip": 6, "auto": 7}


class Shape:
    """Byte length of the wrapper header, bit end of the last block, kind of the header."""

    def __init__(self, layer, source, dict_, bits):
        self.source = source
        if layer == "raw":
            self.kind, self.hlen, body_dict = "raw", 0, F.tail_dict(dict_, 2 ** bits)
        elif source[:2] == b"\x1f\x8b":
            self.kind, p, flg = "gzip", 10, source[3]
            if flg & 4:
                p += 2 + (source[10] | source[11] << 8)
            for bit in (8, 16):
                if flg & bit:
                    p = source.index(b"\0", p) + 1
            self.hcrc_at = p
            if flg & 2:
                p += 2
            self.hlen, body_dict = p, b""
        else:
            self.kind = "zlib"
            fdict = source[1] // 32 % 2
            self.hlen = 6 if fdict else 2
            window = 2 ** (source[0] // 16 + 8) if bits == 0 else 2 ** bits
            body_dict = F.tail_dict(dict_, window) if fdict else b""
        rd = F.Reader(source[self.hlen:])
        out = []
        while not F.block(rd, body_dict, out):
            pass
        self.end = 8 * self.hlen + rd.pos
        self.trailer = (self.end + 7) // 8 * 8
        self.out = bytes(out)


def facts(cfg, shape, log_in, log_out, t, pending):
    wrap, bits = cfg
    (mode, held, hold, swrap, flags, havedict, wbits, check, total, headnull, last, wsize,
     sane) = t
    c = 8 * len(log_in) - held
    F.need(c >= 0 and log_in == shape.source[:len(log_in)], "input is a prefix of the source")
    F.need(swrap == WRAPCODE[wrap], f"wrap {swrap} is the code of {wrap}")
    F.need(headnull == 1 and sane == 1, "no header record, sane")
    F.need(bits == 0 or wbits == bits, f"width {wbits} is the configured {bits}")
    F.need(hold < 2 ** held, "hold has only the held bits")
    name = NAME.get(mode, "?")
    if mode in (M["BAD"], M["MEM"], M["SYNC"]):
        return name
    if mode <= M["DICTID"]:
        F.need(c % 8 == 0 and c < 8 * shape.hlen + (8 if shape.kind == "raw" else 0),
               "header modes: whole header bytes consumed")
        F.need(log_out == b"", "no output in the header")
        F.need(last == 0 and total == 0, "header: no block read, no output counted")
        if shape.kind == "raw":
            F.need(mode == M["HEAD"] and c == 0, "raw: only HEAD before the body")
        else:
            F.need(havedict == 0 and wsize == 0, "wrapped header: no dictionary and no window yet")
        if mode == M["HEAD"]:
            F.need(c == 0 and flags == -1, "HEAD: nothing consumed, flags unread")
        if mode == M["DICTID"]:
            F.need(shape.kind == "zlib" and c == 16, "DICTID after the two zlib bytes")
            F.need(shape.source[1] & 0x20 != 0, "DICTID only with FDICT set")
        if M["FLAGS"] <= mode <= M["HCRC"]:
            F.need(shape.kind == "gzip", "gzip modes only for a gzip header")
            if mode == M["FLAGS"]:
                F.need(c == 16 and flags == -1, "FLAGS after the magic")
            else:
                F.need(flags == shape.source[2] | shape.source[3] << 8, "gzip flags word")
                if flags & 0x200:
                    F.need(check == F.crc32(shape.source[:c // 8]),
                           "FHCRC: check is the CRC-32 of the header bytes so far")
            if mode == M["HCRC"]:
                F.need(c == 8 * shape.hcrc_at, "HCRC after name and comment")
        return name
    if mode == M["DICT"]:
        F.need(shape.kind == "zlib" and c == 48, "DICT after six bytes")
        F.need(check == int.from_bytes(shape.source[2:6], "big"), "DICT: check is DICTID")
        F.need((havedict == 0) == pending, "havedict = 0 exactly while a request is pending")
        F.need(last == 0 and total == 0, "DICT: no block read, no output counted")
        F.need(havedict != 0 or wsize == 0, "DICT without a dictionary: no window yet")
        return name
    expect_flags = {"raw": -1, "zlib": 0}.get(shape.kind)
    if expect_flags is None:
        F.need(flags == shape.source[2] | shape.source[3] << 8, "gzip flags word in the body")
    else:
        F.need(flags == expect_flags, f"flags {flags} for {shape.kind}")
    F.need(total == len(log_out) % 2 ** 64, "total is the output length")
    F.need(shape.out[:len(log_out)] == log_out, "output is a prefix of the decoding")
    if shape.kind != "raw":
        want = F.crc32(log_out) if shape.kind == "gzip" else F.adler32(log_out)
        if mode < M["CHECK"]:
            F.need(check == want, "check is the checksum of the output")
    if mode <= M["LIT"]:
        F.need(8 * shape.hlen <= c <= shape.end, "block modes: consumed bits inside the body")
        if mode in (M["TYPE"], M["TYPEDO"]):
            F.need(held < 8, f"block boundary: {held} bits held")
        return name
    F.need(shape.kind != "raw" or mode == M["DONE"], "raw: no trailer modes")
    if mode == M["CHECK"]:
        F.need(c == shape.trailer and log_out == shape.out, "CHECK at the aligned end of the body")
    elif mode == M["LENGTH"]:
        F.need(shape.kind == "gzip" and c == shape.trailer + 32, "LENGTH after the CRC-32")
    elif mode == M["DONE"]:
        F.need(held == 0 and c == 8 * len(shape.source) and log_out == shape.out,
               "DONE: nothing held, whole source consumed")
    return name


def check_session(lines):
    head = lines[0].split()
    wb, rc = int(head[1]), int(head[2])
    if rc != 0:
        return {}
    cfg = F.infl_wbits(wb)
    layer = valid = source = dict_ = None
    log_in, log_out, pending, single = b"", b"", False, True
    shape, seen, shape_dict = None, {}, b""
    dict_log = b""
    for ln in lines[1:]:
        p = ln.split()
        if p[0] == "G":
            layer, valid = p[1], p[2] == "1"
            source = bytes.fromhex(p[4]) if len(p) > 4 and p[4] != "-" else b""
        elif p[0] == "K":
            dict_ = bytes.fromhex(p[1]) if p[1] != "-" else b""
        elif p[0] == "C":
            k = p.index("->")
            rc = int(p[k + 1])
            used = p[k + 8]
            wrote = p[k + 9]
            if p[3] == "0":
                log_in += bytes.fromhex(used) if used != "-" else b""
            if p[4] == "0":
                log_out += bytes.fromhex(wrote) if wrote != "-" else b""
            if not (int(p[2]) in (-1, 7)) and p[3] == "0" and p[4] == "0":
                pending = rc == 2
            elif rc == 2:
                pending = True
        elif p[0] == "D":
            rc = int(p[1])
            data = bytes.fromhex(p[2]) if p[2] != "-" else b""
            if rc == 0:
                if wb < 0:
                    if log_in or log_out:
                        single = False
                    dict_log += data
                else:
                    dict_log = data
                    pending = False
        elif p[0] == "T":
            t = tuple(int(x) for x in p[1:])
            if not single or not valid or source is None:
                continue
            d = dict_log if wb < 0 else (dict_ or b"")
            if shape is None:
                if F.layer_decodes(cfg[0], cfg[1], d, source) is None:
                    continue
                if not F.full_window(cfg[0], cfg[1], source):
                    continue
                shape = Shape("raw" if cfg[0] == "raw" else "x", source, d, cfg[1])
            elif wb < 0 and F.tail_dict(d, 2 ** cfg[1]) != F.tail_dict(shape_dict, 2 ** cfg[1]):
                continue
            shape_dict = d
            name = facts(cfg, shape, log_in, log_out, t, pending)
            seen[name] = seen.get(name, 0) + 1
    return seen


def main():
    total, sessions, block = {}, 0, []

    def run(block):
        try:
            seen = check_session(block)
        except F.Fail as e:
            print("FAIL:", e)
            print("\n".join(block[:6] + ["..."]))
            sys.exit(1)
        for k, v in seen.items():
            total[k] = total.get(k, 0) + v

    for line in sys.stdin:
        line = line.rstrip("\n")
        if line.startswith("S ") and block:
            run(block)
            sessions += 1
            block = []
        block.append(line)
    if block:
        run(block)
        sessions += 1
    print(f"{sessions} sessions; checked states per mode:",
          " ".join(f"{k}={v}" for k, v in sorted(total.items(), key=lambda kv: M.get(kv[0], 0))))


if __name__ == "__main__":
    main()
