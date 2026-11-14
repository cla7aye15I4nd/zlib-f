#!/usr/bin/env python3
"""Semantic proof mutants of inflateBack for Goal.inflate_back_sequence_safety.

Usage: python3 tests/proof-mutants/infback-sequence.py <copy of the workspace> <mutant name>
then `lake build` the modules the row of tests/proof-mutants/infback-sequence.tsv names, in that copy.

Each mutant changes one thing in the translation (ZlibF/Zlib/infback.c.lean). The call proof restates the
end of `inflateBack()` (`backTail`, `infback.c.safety-call`), and `inflateBack_eq` checks the restatement
by `rfl`. This script makes the same edit there, as a person repairing the proof would, so that only a
semantic lemma can fail: the result of the call. Every listed edit must apply exactly once.
"""
import sys, pathlib
w = pathlib.Path(sys.argv[1]); name = sys.argv[2]
Z = 'ZlibF/Zlib/infback.c.lean'
CALL = 'ZlibF/Proof/infback.c.safety-call.lean'
M = {
 # inflateBack: a refused last partial window after the end of the stream returns Z_OK, not Z_BUF_ERROR.
 'inflateBack-flush-failure-ok': [(f, '&& ret == Z_STREAM_END then ret := Z_BUF_ERROR',
                                   '&& ret == Z_STREAM_END then ret := Z_OK') for f in [Z, CALL]],
}
for f, old, new in M[name]:
    p = w / f; s = p.read_text()
    if s.count(old) != 1: sys.exit(f'not exactly once in {f}: {old}')
    p.write_text(s.replace(old, new))
    print(f, 1)
