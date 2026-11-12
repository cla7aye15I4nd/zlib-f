#!/usr/bin/env python3
"""Semantic proof mutants of the deflate operations (deflateSetDictionary, deflateParams, deflateCopy).

Usage: python3 tests/proof-mutants/deflate-ops.py <copy of the workspace> <mutant name>
then `lake build` the module the row of tests/audit/proofmut/deflate.tsv names, in that copy.

Each mutant changes one thing in the translation (ZlibF/Zlib/deflate.c.lean). The operation proofs restate
the code they run (`setdict_source`, `setdict_split`, `setdictTail`, `setdictWrites`, `params_source`,
`paramsTail`, `copyTail`, `copyCnt`, the case splits on the range check) and name the end state
(`setdictEnd`, `paramsFinal`). This script makes the same edit there, as a person repairing the proof
would, so that only a semantic lemma can fail: a bound, the range of the level, or the invariant of the
end state. Every listed edit must apply at least once.
"""
import sys, pathlib
w = pathlib.Path(sys.argv[1]); name = sys.argv[2]
P = 'ZlibF/Proof/'
Z = 'ZlibF/Zlib/deflate.c.lean'
DICT = P + 'deflate.c.universal-ops-dictionary.lean'
COPY = P + 'deflate.c.universal-ops-copy.lean'
PAR = P + 'deflate.c.universal-ops-params.lean'
PARG = P + 'deflate.c.universal-ops-params-general.lean'
HOPS = P + 'deflate.c.universal-header-ops.lean'
VIEW = P + 'deflate.c.universal-ops-dictionary-view.lean'
# the count of skipped dictionary bytes, restated for the mutant (a true equation; the bounds that use it fail)
SKIP = '(len - d.w_size).toNat = len.toNat - d.w_size.toNat :=\n      UInt32.toNat_sub_of_le _ _ big'
SKIP1 = ('(len - d.w_size + 1).toNat = (len.toNat - d.w_size.toNat + 1) % 2 ^ 32 := by\n'
         '      rw [UInt32.toNat_add, UInt32.toNat_sub_of_le _ _ big]; rfl')
RANGE = 'if level < 0 || level > 9 || strategy < 0 || strategy > Z_FIXED then'
SPLIT = 'decide ((if level == Z_DEFAULT_COMPRESSION then 6 else level) > 9)'
M = {
 # deflateSetDictionary: the long dictionary starts one byte too late (reads past its end).
 'sd-dict-offset': [(f, '(dictLength - d.w_size).toNat', '(dictLength - d.w_size + 1).toNat') for f in [Z, DICT]]
   + [(f, SKIP, SKIP1) for f in [DICT, VIEW]]
   + [(f, '(len - d.w_size).toNat', '(len - d.w_size + 1).toNat') for f in [DICT, VIEW]],
 # deflateSetDictionary: insert counts one byte more than the dictionary left in the window.
 'sd-insert': [(f, 'insert := d.lookahead,', 'insert := d.lookahead + 1,') for f in [Z, DICT]]
   + [(DICT, 'insert := e1.lookahead,', 'insert := e1.lookahead + 1,'),
      (DICT, 'have insF : dF.insert = d2.lookahead := rfl', 'have insF : dF.insert = d2.lookahead + 1 := rfl')],
 # deflateParams: level 10 is accepted.
 'params-level-hi': [(f, RANGE, RANGE.replace('level > 9', 'level > 10')) for f in [Z, PAR]]
   + [(f, SPLIT, SPLIT.replace('> 9)', '> 10)')) for f in [PAR, PARG, HOPS]]
   + [(f, 'decide (lv > 9)', 'decide (lv > 10)') for f in [PAR, HOPS]]
   + [(f, 'change ¬ (9 : Int) < lv.toInt', 'change ¬ (10 : Int) < lv.toInt') for f in [PAR, HOPS]],
 # deflateParams: the repaired level-0 table keeps one pending slide in matches.
 'params-matches': [(Z, '      wr s (fun d => { d with «matches» := 0 })\n    -- s->level',
                        '      wr s (fun d => { d with «matches» := 1 })\n    -- s->level'),
                    (PAR, '      wr s (fun d => { d with «matches» := 0 })', '      wr s (fun d => { d with «matches» := 1 })'),
                    (PARG, '{ d with «matches» := 0, slid := s }', '{ d with «matches» := 1, slid := s }'),
                    (PARG, 'show (0 : UInt32).toNat ≤ 2 by decide, fun _ => rfl', 'show (1 : UInt32).toNat ≤ 2 by decide, fun _ => rfl')],
 # deflateCopy: one window byte more than high_water is copied.
 'copy-window-count': [(f, 'memcpyB window sd.window sd.high_water.toNat', 'memcpyB window sd.window (sd.high_water.toNat + 1)')
                       for f in [Z, COPY]],
 # deflateCopy: one prev slot more than w_size after a slide.
 'copy-prev-count': [(f, 'then dd.w_size else', 'then dd.w_size + 1 else') for f in [Z, COPY]],
 # deflateCopy: the pending cursor of the copy is one byte off.
 'copy-pending-offset': [(f, 'Ptr.add pending_buf off.toInt', 'Ptr.add pending_buf (off.toInt + 1)') for f in [Z, COPY]],
}
for f, old, new in M[name]:
    p = w / f; s = p.read_text()
    if old not in s: sys.exit(f'missing in {f}: {old}')
    p.write_text(s.replace(old, new))
    print(f, s.count(old))
