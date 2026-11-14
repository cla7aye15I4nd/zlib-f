#!/usr/bin/env python3
"""Semantic proof mutants of the gz file interface for Goal.gz_sequence_safety.

Usage: python3 tests/proof-mutants/gz-sequence.py <copy of the workspace> <mutant name>
then `lake build` the modules the row of tests/proof-mutants/gz-sequence.tsv names, in that copy.

Each mutant changes one thing in a translation (gzwrite.c, gzread.c, gzlib.c, zlib.h). The gz proofs restate the
code they run, in pieces named after the source (`gzwrite_eq`, `putcSlow`, `closeTail`, `pfFmt`, `gTail`, `tSkip`,
`seekTail`, `openAfterMode`, `fetchBody`, `restK`, `getsRest`, the private copies of `gz_error`, ...), and check the
restatement by `rfl`. This script makes the same edit there, as a person repairing the proof would, so that only a
semantic lemma can fail: the invariant, the frame, a release, or the absence of a fault. Every listed edit must
apply at least once. The rows named patch000N-* each remove one hunk of a patch (the unpatched C).
"""
import sys, pathlib
w = pathlib.Path(sys.argv[1]); name = sys.argv[2]
P = 'ZlibF/Proof/'
ZW = 'ZlibF/Zlib/gzwrite.c.lean'
ZR = 'ZlibF/Zlib/gzread.c.lean'
ZL = 'ZlibF/Zlib/gzlib.c.lean'
ZH = 'ZlibF/Zlib/zlib.h.lean'
WC = P + 'gzwrite.c.write-calls.lean'
WR = P + 'gzwrite.c.write.lean'
PF = P + 'gzwrite.c.printf.lean'
FP = P + 'gzwrite.c.flush-params.lean'
CL = P + 'gzwrite.c.close.lean'
GC = P + 'gzread.c.getc-ungetc.lean'
GS = P + 'gzread.c.skip-gets.lean'
GT = P + 'gz.read-gets-step.lean'
GD = P + 'gz.read-direct-step.lean'
FE = P + 'gz.read-fetch.lean'
LK = P + 'gz.read-look.lean'
RD = P + 'gz.read-read.lean'
SK = P + 'gzlib.c.seek.lean'
OM = P + 'gzlib.c.open-mode.lean'
OI = P + 'gzlib.c.open-io.lean'
OC = P + 'gzlib.c.open-copy-stage.lean'
DE = P + 'gzlib.c.dopen-entry.lean'
ERR = [P + 'gzlib.c.error-borrow.lean', P + 'gzlib.c.error-keeps-x.lean', P + 'gzlib.c.error-noescape.lean']
MAC = P + 'zlib.h.gzgetc-macro.lean'
GW = 'if s.mode != GZ_WRITE || (s.err != Z_OK && s.again == 0) then '
NW = 'if s.err != Z_OK && s.again == 0 then '
EOK = 'gz_error (gzSt i) Z_OK .null\n'
LOAD = 'if r == -1 then return some (-1)\n'
M = {
 # gzwrite: the mode test is dropped (a write on a reader).
 'gzwrite-mode-check-dropped': [(ZW, GW + 'return 0\n  gz_error state Z_OK .null\n  -- if ((int)len < 0)',
                                 NW + 'return 0\n  gz_error state Z_OK .null\n  -- if ((int)len < 0)'),
                                (WC, GW + 'return 0\n      Zlib.Gzlib.' + EOK + '      if len.toInt32',
                                 NW + 'return 0\n      Zlib.Gzlib.' + EOK + '      if len.toInt32')],
 # gzfwrite: the mode test is dropped.
 'gzfwrite-mode-check-dropped': [(ZW, GW + 'return 0\n  gz_error state Z_OK .null\n  -- len = nitems',
                                  NW + 'return 0\n  gz_error state Z_OK .null\n  -- len = nitems'),
                                 (WC, GW + 'return 0\n      Zlib.Gzlib.' + EOK + '      let len := nitems',
                                  NW + 'return 0\n      Zlib.Gzlib.' + EOK + '      let len := nitems')],
 # gzputs: the mode test is dropped.
 'gzputs-mode-check-dropped': [(ZW, GW + 'return -1\n  gz_error state Z_OK .null\n  -- len = strlen(s);',
                                NW + 'return -1\n  gz_error state Z_OK .null\n  -- len = strlen(s);'),
                               (WC, GW + 'return -1\n      Zlib.Gzlib.' + EOK + '      let len ← strlenB str',
                                NW + 'return -1\n      Zlib.Gzlib.' + EOK + '      let len ← strlenB str')],
 # gzputc: the local one-byte block of the slow path is not freed.
 'gzputc-local-free-skipped': [(f, '  freeB buf\n  if w != 1 then return -1', '  pure ()\n  if w != 1 then return -1')
                               for f in [ZW, WC]],
 # gzvprintf (and gzprintf): a formatted length of size or more is accepted.
 'gzvprintf-length-check-dropped': [(f, 'if len == 0 || len.toUInt32 ≥ s.size then return 0', 'if len == 0 then return 0')
                                    for f in [ZW, PF]],
 # gzflush: the mode test is dropped.
 'gzflush-mode-check-dropped': [(ZW, GW + 'return Z_STREAM_ERROR\n  gz_error state Z_OK .null\n  -- if (flush < 0',
                                 NW + 'return Z_STREAM_ERROR\n  gz_error state Z_OK .null\n  -- if (flush < 0'),
                                (FP, GW + 'return Z_STREAM_ERROR\n      Zlib.Gzlib.' + EOK + '      if flush < 0',
                                 NW + 'return Z_STREAM_ERROR\n      Zlib.Gzlib.' + EOK + '      if flush < 0')],
 # gzsetparams: the mode test is dropped.
 'gzsetparams-mode-check-dropped': [(f, 'if s.mode != GZ_WRITE || (s.err != Z_OK && s.again == 0) || s.direct != 0 then',
                                     'if (s.err != Z_OK && s.again == 0) || s.direct != 0 then') for f in [ZW, FP]],
 # gzclose_w: deflateEnd is skipped (the deflate state leaks).
 'gzclose_w-deflateEnd-skipped': [(ZW, 'let _ ← deflateEnd (strmOf state)', 'pure ()'),
                                  (CL, 'let _ ← Zlib.Deflate.deflateEnd (strmOf (gzSt i))', 'pure ()')],
 # gzclose_w: the input buffer is not freed.
 'gzclose_w-in-free-skipped': [(ZW, '    freeB s.«in»\n  -- gz_error(state, Z_OK, NULL);', '    pure ()\n  -- gz_error(state, Z_OK, NULL);'),
                               (CL, '    freeB s.«in»\n  Zlib.Gzlib.gz_error', '    pure ()\n  Zlib.Gzlib.gz_error')],
 # gzclose_w: the path is not freed.
 'gzclose_w-path-free-skipped': [(ZW, '  freeB s.path\n  -- if (close(state->fd)', '  pure ()\n  -- if (close(state->fd)'),
                                 (CL, '  freeB s.path\n  if (← fsClose s.fd)', '  pure ()\n  if (← fsClose s.fd)')],
 # gzclose_w: the descriptor is not closed.
 'gzclose_w-descriptor-kept': [(f, 'if (← fsClose s.fd) == -1 then ret := Z_ERRNO', 'if false then ret := Z_ERRNO')
                               for f in [ZW, CL]],
 # gz_open: a mode string with no r, w or a leaks the record.
 'gz_open-no-mode-leak': [(f, 'if s.mode == GZ_NONE then\n    freeGzState state', 'if s.mode == GZ_NONE then\n    pure ()')
                          for f in [ZL, OM]]
                         + [(f, 'if s.mode == GZ_NONE then\n      freeGzState state', 'if s.mode == GZ_NONE then\n      pure ()')
                            for f in [OI, OC]],
 # gz_open: a failed open leaks the path.
 'gz_open-open-failure-path-leak': [(f, '  if s.fd == -1 then\n    freeB s.path\n    freeGzState state',
                                     '  if s.fd == -1 then\n    pure ()\n    freeGzState state') for f in [ZL, OM, OI]],
 # gz_open: gz_reset is skipped (x.have, x.pos, skip, err left as allocated).
 'gz_open-reset-skipped': [(f, '  gz_reset state\n  return castFile state', '  pure ()\n  return castFile state')
                           for f in [ZL, OM, OI]],
 # gzdopen: the formatted path is not freed.
 'gzdopen-path-leak': [(f, '  let gz ← gz_open path fd mode\n  freeB path', '  let gz ← gz_open path fd mode\n  pure ()')
                       for f in [ZL, DE]],
 # gzseek64: a forward seek in the buffer advances x.next and x.pos but keeps x.have.
 'gzseek64-have-not-consumed': [(f, 'updX state fun x => { x with «have» := x.«have» - n }', 'pure ()') for f in [ZL, SK]],
 # gzseek64: the pending skip is the target position, not the remaining offset.
 'gzseek64-skip-wrong': [(f, 'updS state fun s => { s with skip := offset }', 'updS state fun s => { s with skip := pos }')
                         for f in [ZL, SK]],
 # patch 0005, gzseek64: x.next is advanced also by 0.
 'patch0005-seek-next-unconditional': [(f, 'if n != 0 then', 'if true then') for f in [ZL, SK]],
 # gz_error: the previous message is not freed.
 'gz_error-free-skipped': [(f, 'if s.err != Z_MEM_ERROR then freeB s.msg', 'if s.err != Z_MEM_ERROR then pure ()')
                           for f in [ZL] + ERR],
 # gz_error: Z_MEM_ERROR also allocates a message (which the next gz_error does not free).
 'gz_error-mem-error-message': [(f, 'if err == Z_MEM_ERROR then return', 'if false then return') for f in [ZL] + ERR],
 # the gzgetc() macro: the have test is dropped.
 'macro-have-guard-dropped': [(ZH, '  if s.x.«have» != 0 then\n    -- (g)->have--,', '  if true then\n    -- (g)->have--,'),
                              (MAC, '    if s.x.«have» != 0 then\n      updX', '    if true then\n      updX')],
 # the gzgetc() macro: x.pos is not advanced.
 'macro-pos-not-advanced': [(ZH, '    let np ← i64add s.x.pos 1\n    updX state fun x => { x with pos := np }\n',
                             '    let np ← i64add s.x.pos 1\n'),
                            (MAC, '      let np ← i64add s.x.pos 1\n      updX (some (.tab i)) fun x => { x with pos := np }\n',
                             '      let np ← i64add s.x.pos 1\n')],
 # gzgetc: the buffered path does not decrement x.have.
 'gzgetc-have-not-decremented': [(f, 'updX state fun x => { x with «have» := x.«have» - 1 }', 'pure ()') for f in [ZR, GC]],
 # gzungetc: the buffered bytes are not slid to the end of out.
 'gzungetc-slide-skipped': [(f, 'if s.x.next == s.out then', 'if false then') for f in [ZR, GC]],
 # gzgets: left counts the whole length, so the final NUL can go past the buffer.
 'gzgets-left-whole-length': [(f, 'let left : UInt32 := len.toUInt32 - 1', 'let left : UInt32 := len.toUInt32') for f in [ZR, GS]],
 # gzgets: the mode test is dropped.
 'gzgets-mode-check-dropped': [(f, 'if s.mode != GZ_READ then return .null', 'if false then return .null') for f in [ZR, GT]],
 # gzdirect: the mode test is dropped (gz_look on a writer).
 'gzdirect-mode-check-dropped': [(f, 'if s.mode == GZ_READ && s.how == LOOK && s.x.«have» == 0 then',
                                  'if s.how == LOOK && s.x.«have» == 0 then') for f in [ZR, GD]],
 # patch 0003, gz_fetch COPY: x.next is set after gz_load, so a failed load leaves it stale.
 'patch0003-copy-next-after-load': [
   (ZR, '        updX state fun x => { x with next := s.out }\n'
        '        -- if (gz_load(state, state->out, room ? room : 1, &(state->x.have)) == -1) return -1;\n'
        '        let s ← ldS state\n'
        '        let (r, hv) ← gz_load state s.out (if room != 0 then room else 1)\n'
        '        updX state fun x => { x with «have» := hv }\n        ' + LOAD,
        '        -- if (gz_load(state, state->out, room ? room : 1, &(state->x.have)) == -1) return -1;\n'
        '        let s ← ldS state\n'
        '        let (r, hv) ← gz_load state s.out (if room != 0 then room else 1)\n'
        '        updX state fun x => { x with «have» := hv }\n        ' + LOAD +
        '        updX state fun x => { x with next := s.out }\n'),
   (FE, '        updX (some (.tab i)) fun x => { x with next := s.out }\n'
        '        let s ← ldS (some (.tab i))\n'
        '        let (r, hv) ← Zlib.Gzread.gz_load (some (.tab i)) s.out (if room != 0 then room else 1)\n'
        '        updX (some (.tab i)) fun x => { x with «have» := hv }\n        ' + LOAD,
        '        let s ← ldS (some (.tab i))\n'
        '        let (r, hv) ← Zlib.Gzread.gz_load (some (.tab i)) s.out (if room != 0 then room else 1)\n'
        '        updX (some (.tab i)) fun x => { x with «have» := hv }\n        ' + LOAD +
        '        updX (some (.tab i)) fun x => { x with next := s.out }\n')],
 # patch 0004, gz_look: all pending input is buffered in COPY mode, past GZ_OFF_MAX.
 'patch0004-look-room-removed': [
   (ZR, '  let room ← gz_room state z.avail_in\n  updX state fun x => { x with «have» := room }\n',
        '  updX state fun x => { x with «have» := z.avail_in }\n'),
   (LK, '  let room ← StateT.lift (Zlib.Gzread.gz_room (some (.tab i)) z.avail_in)\n'
        '  StateT.lift (updX (some (.tab i)) fun x => { x with «have» := room })\n',
        '  StateT.lift (updX (some (.tab i)) fun x => { x with «have» := z.avail_in })\n')],
 # patch 0004, gz_fetch COPY: a full buffer is loaded, past GZ_OFF_MAX.
 'patch0004-fetch-copy-room-removed': [
   (ZR, 'let (r, hv) ← gz_load state s.out (if room != 0 then room else 1)', 'let (r, hv) ← gz_load state s.out (s.size <<< 1)'),
   (FE, 'let (r, hv) ← Zlib.Gzread.gz_load (some (.tab i)) s.out (if room != 0 then room else 1)',
        'let (r, hv) ← Zlib.Gzread.gz_load (some (.tab i)) s.out (s.size <<< 1)')],
 # patch 0004, gz_fetch GZIP: a full buffer is decompressed, past GZ_OFF_MAX.
 'patch0004-fetch-gzip-room-removed': [(f, 'avail_out := if room != 0 then room else 1, next_out := s.out',
                                        'avail_out := s.size <<< 1, next_out := s.out') for f in [ZR, FE]],
 # patch 0004, gz_read: n is not cut to the room before GZ_OFF_MAX (the n == 0 test is then dead).
 'patch0004-read-room-removed': [(ZR, '\n      n ← gz_room state n\n', '\n'),
                                 (RD, '  let n ← Zlib.Gzread.gz_room (some (.tab i)) n0\n', '  let n := n0\n')],
 # patch 0004, gzgets: n is not cut to the room before GZ_OFF_MAX (the n == 0 test is then dead).
 'patch0004-gets-room-removed': [(ZR, '\n        n ← gz_room state n\n', '\n'),
                                 (GS, '\n  n ← Zlib.Gzread.gz_room state n\n', '\n')],
 # patch 0004, gz_write: the position test is dropped.
 'patch0004-write-position-check-removed': [
   (ZW, 'if (← i64sub GZ_OFF_MAX (← ldS state).x.pos).toUInt64 < len then', 'if false then'),
   (WR, 'if (← i64sub GZ_OFF_MAX (← ldS (gzSt i)).x.pos).toUInt64 < len then', 'if false then')],
 # patch 0004, gzputc: the fast path does not test the position.
 'patch0004-putc-position-check-removed': [(f, 'if hv < s.size && s.x.pos < GZ_OFF_MAX then', 'if hv < s.size then')
                                           for f in [ZW, WC]],
 # patch 0004, gzvprintf (and gzprintf): the position test is dropped.
 'patch0004-printf-position-check-removed': [
   (ZW, 'if (← i64sub GZ_OFF_MAX (← ldS state).x.pos) < len.toInt64 then', 'if false then'),
   (PF, 'if (← i64sub GZ_OFF_MAX (← ldS (gzSt i)).x.pos) < len.toInt64 then', 'if false then')],
}
for f, old, new in M[name]:
    p = w / f; s = p.read_text()
    if old not in s: sys.exit(f'missing in {f}: {old}')
    if f.startswith('ZlibF/Zlib/') and s.count(old) != 1: sys.exit(f'not exactly once in {f}: {old}')
    p.write_text(s.replace(old, new))
    print(f, s.count(old))
