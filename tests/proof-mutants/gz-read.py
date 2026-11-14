#!/usr/bin/env python3
"""Semantic proof mutants of the gz read side (gzread, gzfread, gzgetc, gzungetc).

Usage: python3 tests/proof-mutants/gz-read.py <copy of the workspace> <mutant name>
then `lake build` the module the row of tests/proof-mutants/gz-read.tsv names, in that copy.

Each mutant changes one thing in the translation (ZlibF/Zlib/gzread.c.lean). The read proofs restate the
code they run by `rfl` (`gzread_eq`, `rdRest`, `rdAfter`, `gzfread_eq`, `frRest`, `gzgetc_eq`, `gTail`,
`gzungetc_eq`, `tLook`, `tAgain`, `tSkip`). This script makes the same edit there, as a person repairing
the proof would, so that only a semantic lemma can fail: the reader mode, the caller's region, the
buffer bounds, the pending skip or the ledger. Every listed edit must apply exactly once.
"""
import sys, pathlib
w = pathlib.Path(sys.argv[1]); name = sys.argv[2]
P = 'ZlibF/Proof/'
Z = 'ZlibF/Zlib/gzread.c.lean'
RD = P + 'gz.read-gzread.lean'
FR = P + 'gzread.c.fread.lean'
GU = P + 'gzread.c.getc-ungetc.lean'
GZERR = '\n      if s.err != Z_OK && s.err != Z_BUF_ERROR && s.again == 0 && s.x.«have» == 0 then return '
M = {
 # gzread: the reader-mode refusal is dropped (a writer handle reaches gz_read).
 'gzread-mode-check': [
   (Z, '  if s.mode != GZ_READ then return -1\n  -- if (state->err != Z_OK && state->err != Z_BUF_ERROR',
       '  if false then return -1\n  -- if (state->err != Z_OK && state->err != Z_BUF_ERROR'),
   (RD, '      if s.mode != GZ_READ then return -1' + GZERR + '-1',
        '      if false then return -1' + GZERR + '-1')],
 # gzread: the `(int)len < 0` refusal is dropped (gz_read writes 2^31 bytes or more).
 'gzread-int-check': [(f, '  if len.toInt32 < 0 then', '  if false then') for f in [Z, RD]],
 # gzread: the `(int)len < 0` refusal is off by one (len = 0xffffffff reaches gz_read).
 'gzread-int-check-off-by-one': [(f, '  if len.toInt32 < 0 then', '  if len.toInt32 < -1 then') for f in [Z, RD]],
 # gzfread: the reader-mode refusal is dropped.
 'gzfread-mode-check': [
   (Z, '  if s.mode != GZ_READ then return 0\n', '  if false then return 0\n'),
   (FR, '      if s.mode != GZ_READ then return 0' + GZERR + '0',
        '      if false then return 0' + GZERR + '0')],
 # gzfread: the size_t overflow refusal is dropped (gz_read gets the wrapped product).
 'gzfread-overflow-check': [(f, '  if size != 0 && len / size != nitems then', '  if false then') for f in [Z, FR]],
 # gzfread: the overflow test compares the wrong way (a wrapped product is below nitems and passes).
 'gzfread-overflow-compare': [(f, '  if size != 0 && len / size != nitems then',
                                  '  if size != 0 && len / size > nitems then') for f in [Z, FR]],
 # gzgetc: the reader-mode refusal is dropped.
 'gzgetc-mode-check': [
   (Z, '  if s.mode != GZ_READ then return -1' + GZERR.replace('      ', '  ') + '-1\n  if s.again != 0 then gz_error state Z_OK .null\n  -- if (state->x.have)',
       '  if false then return -1' + GZERR.replace('      ', '  ') + '-1\n  if s.again != 0 then gz_error state Z_OK .null\n  -- if (state->x.have)'),
   (GU, '    if s.mode != GZ_READ then return -1\n    if s.err != Z_OK',
        '    if false then return -1\n    if s.err != Z_OK')],
 # gzgetc: the buffered-byte path is taken with no buffered byte (reads *x.next with have = 0).
 'gzgetc-have-check': [(f, '  if s.x.«have» != 0 then\n    updX state fun x => { x with «have» := x.«have» - 1 }',
                           '  if true then\n    updX state fun x => { x with «have» := x.«have» - 1 }') for f in [Z, GU]],
 # gzgetc: the one-byte local buffer is not freed (leak).
 'gzgetc-local-leak': [(f, '  freeB buf\n  return r', '  return r') for f in [Z, GU]],
 # gzungetc: the reader-mode refusal is dropped.
 'gzungetc-mode-check': [
   (Z, '  if s.mode != GZ_READ then return -1\n  -- if (state->how == LOOK && state->x.have == 0)',
       '  if false then return -1\n  -- if (state->how == LOOK && state->x.have == 0)'),
   (GU, '    if s.mode != GZ_READ then return -1\n    if s.how == LOOK',
        '    if false then return -1\n    if s.how == LOOK')],
 # gzungetc: the pending skip is not processed before the push.
 'gzungetc-skip-dropped': [
   (Z, '  if (← ldS state).skip != 0 then\n    if (← gz_skip state) == -1 then return -1\n  -- if (c < 0) return -1;',
       '  if false then\n    if (← gz_skip state) == -1 then return -1\n  -- if (c < 0) return -1;'),
   (GU, '  if (← ldS state).skip != 0 then\n    if (← Zlib.Gzread.gz_skip state) == -1 then return -1\n  tSkip c state',
        '  if false then\n    if (← Zlib.Gzread.gz_skip state) == -1 then return -1\n  tSkip c state')],
 # gzungetc: the full-buffer refusal is dropped (a push with have = 2 * size writes before out).
 'gzungetc-full-check': [(f, '  if s.x.«have» == (s.size <<< 1) then', '  if false then') for f in [Z, GU]],
 # gzungetc: the first pushed byte is stored one past the end of out (off by one).
 'gzungetc-empty-offset': [(f, '    let p ← (← s.out.add (s.size <<< 1).toNat).add (-1)',
                               '    let p ← (← s.out.add (s.size <<< 1).toNat).add 0') for f in [Z, GU]],
}
for f, old, new in M[name]:
    p = w / f; s = p.read_text()
    if s.count(old) != 1: sys.exit(f'{s.count(old)} occurrences in {f}: {old!r}')
    p.write_text(s.replace(old, new))
    print(f, 1)
