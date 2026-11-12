#!/usr/bin/env python3
"""Semantic proof mutants of batch C (the deflate header stages and _tr_flush_block).

Usage: python3 tests/proof-mutants/deflate-header.py <copy of the workspace> <mutant name>
then `lake build` the targets of tests/proof-mutants/deflate-header.tsv in that copy.

Each mutant changes one check in the translation (ZlibF/Zlib). The proofs restate the code they reason
about (the phase and stage splits, `delta ...; exact rfl`, and the case splits on the code's
conditions), so a plain mutant is caught by those restatements and shows nothing. This script makes the
same edit in every restatement and in the case splits on the mutated condition, as a person repairing
the proof would. The mutant counts only if the first error is then in a semantic lemma: a room bound or
a NULL case (deflate-header.tsv records where). For deflate-string-full-check the branch the mutated
condition makes impossible (pending above the buffer size) is left unproved in the throwaway copy, so
the first error is the room bound of the other branch.
"""
# that code, and the repair of the proof's case split on the mutated condition
import sys, pathlib
w = pathlib.Path(sys.argv[1]); name = sys.argv[2]
P = 'ZlibF/Proof/'
E = 'd.pending + st.left > d.pending_buf_size'
H = 'd.pending + 2 > d.pending_buf_size then'
S = 'if d.pending == d.pending_buf_size then'
T = 'if stored_len + 4 ≤ opt_lenb ∧ buf != .null then'
TC = [P+f for f in ['deflate.c.engine.block-prepare.lean', 'deflate.c.engine.flush-dynamic.lean',
      'trees.c.dynamic-header.lean', 'trees.c.flush-source.lean']] + ['ZlibF/Zlib/trees.c.lean']
CS = 'by_cases chooseStored : len + (4 : UInt64) ≤\n      selectedCost (byteCost prepared.opt_len) (byteCost prepared.static_len) (prepared.strategy == Z_FIXED) ∧\n      source != .null'
M = {
 'deflate-extra-room': [(f, E, E + ' + 1') for f in ['ZlibF/Zlib/deflate.c.lean', P+'deflate.c.engine.public-source.lean',
     P+'deflate.c.universal-call-phases.lean', P+'deflate.c.universal-call-stages.lean', P+'deflate.c.universal-call-extra.lean']]
   + [(P+'deflate.c.universal-call-extra.lean', 'd1.pending + st.left > d1.pending_buf_size', 'd1.pending + st.left > d1.pending_buf_size + 1'),
      (P+'deflate.c.universal-call-extra.lean', 'rw [UInt64.toNat_add, Nat.mod_eq_of_lt noWrap] at this',
       'simp only [UInt64.toNat_add, Nat.mod_eq_of_lt noWrap, show (1 : UInt64).toNat = 1 from rfl, Nat.mod_eq_of_lt (show d1.pending_buf_size.toNat + 1 < 2 ^ 64 by omega)] at this')],
 'deflate-hcrc-room': [(f, H, 'd.pending + 1 > d.pending_buf_size then') for f in ['ZlibF/Zlib/deflate.c.lean',
     P+'deflate.c.engine.public-source.lean', P+'deflate.c.universal-call-phases.lean', P+'deflate.c.universal-call-stages.lean',
     P+'deflate.c.universal-call-hcrc.lean']]
   + [(P+'deflate.c.universal-call-hcrc.lean', 'by_cases big : d.pending + 2 > d.pending_buf_size', 'by_cases big : d.pending + 1 > d.pending_buf_size'),
      (P+'deflate.c.universal-call-hcrc.lean', 'show (2 : UInt64).toNat = 2 from rfl', 'show (1 : UInt64).toNat = 1 from rfl')],
 'deflate-string-full-check': [(f, S, 'if d.pending == d.pending_buf_size + 1 then') for f in ['ZlibF/Zlib/deflate.c.lean',
     P+'deflate.c.universal-call-string.lean']]
   + [(P+'deflate.c.universal-call-string.lean', 'by_cases full : d.pending = d.pending_buf_size', 'by_cases full : d.pending = d.pending_buf_size + 1'),
      (P+'deflate.c.universal-call-string.lean', 'have fullN : d.pending.toNat = buf.size := by rw [full, psize]', 'have fullN : d.pending.toNat = buf.size := by sorry')],
 'tr-flush-stored-null': [(f, T, 'if stored_len + 4 ≤ opt_lenb then') for f in TC]
   + [(P+'trees.c.universal-block.lean', CS, CS.replace('source != .null', 'True'))]
   + [(f, ' ∧ source != .null)', ')') for f in [P+'deflate.c.engine.fixed-clear.lean', P+'deflate.c.engine.flush-dynamic.lean', P+'trees.c.universal-block.lean']]
   + [(P+'deflate.c.engine.flush-default.lean', ' ∧\n          defaultStoredSource d w != .null)', ')'),
      (P+'deflate.c.engine.flush-default.lean', '      defaultStoredSource d w != .null\n  · have nonnegative', '      True\n  · have nonnegative')],
 'tr-flush-stored-room': [(f, T, 'if stored_len + 3 ≤ opt_lenb ∧ buf != .null then') for f in TC]
   + [(f, '+ (4 : UInt64) ≤', '+ (3 : UInt64) ≤') for f in [P+'deflate.c.engine.fixed-clear.lean', P+'deflate.c.engine.flush-dynamic.lean',
       P+'deflate.c.engine.flush-stored.lean', P+'trees.c.universal-block.lean']],
}
for f, old, new in M[name]:
    p = w / f; s = p.read_text()
    if old not in s: sys.exit(f'missing in {f}: {old}')
    p.write_text(s.replace(old, new))
    print(f, s.count(old))
