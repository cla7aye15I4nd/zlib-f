#!/usr/bin/env python3
"""Actual build_bl_tree rejects synchronized scan, search and cost mutants."""
from pathlib import Path
import os
import re
import shutil
import subprocess
import tempfile


def main():
    root = Path(__file__).resolve().parents[2]
    source = Path('ZlibF/Zlib/trees.c.lean')
    proof = Path('ZlibF/Proof/trees.c.bl-tree.lean')
    originals = {p: (root / p).read_text() for p in (source, proof)}
    variants = (
        ('wrong-first-tree', 'blScanPair',
         'scan_tree s (← pLtree s) (← rd s).l_desc.max_code',
         'scan_tree s (← pDtree s) (← rd s).l_desc.max_code', 'bl_scan_pair'),
        ('dropped-distance-scan', 'blScanPair',
         'scan_tree s (← pDtree s) (← rd s).d_desc.max_code', 'pure ()', 'bl_scan_pair'),
        ('dropped-bit-length-construction', 'blBuild',
         'build_tree s (← pBldesc s)', 'pure ()', 'bl_build'),
        ('wrong-loop-boundary', 'blIndexLoop',
         'mb.toInt ≥ 3', 'mb.toInt ≥ 4', 'ws_blIndexLoop'),
        ('reversed-used-test', 'blIndexBody',
         '(u8i (← blOrder mb.toInt)).toInt) != 0',
         '(u8i (← blOrder mb.toInt)).toInt) == 0', 'ws_blIndexBody'),
        ('doubled-decrement', 'blIndexBody',
         'isub mb 1', 'isub mb 2', 'ws_blIndexBody'),
        ('skipped-first-rank', 'blIndexLoop',
         '(BL_CODES - 1, false)', '(BL_CODES - 2, false)', 'ws_blIndexLoop'),
        ('wrong-header-cost', 'blFinish',
         'opt_len := d.opt_len + (3 * (i2ul mb + 1) + 5 + 5 + 4)',
         'opt_len := d.opt_len + (4 * (i2ul mb + 1) + 5 + 5 + 4)', 'ws_blFinish'),
    )
    env = os.environ.copy()
    env['LC_ALL'] = 'C'

    def build(where, equality=False):
        target = 'ZlibF.Proof.«trees.c.bl-tree»' if equality else 'ZlibF.Proof.«trees.c.bl-support»'
        return subprocess.run(['lake', 'build', target],
                              cwd=where, env=env, text=True, stdout=subprocess.PIPE,
                              stderr=subprocess.STDOUT, timeout=600)

    with tempfile.TemporaryDirectory(prefix='trees-bl-tree-') as name:
        scratch = Path(name)
        for f in ('lakefile.toml', 'lean-toolchain'):
            shutil.copy2(root / f, scratch / f)
        shutil.copytree(root / 'ZlibF', scratch / 'ZlibF')
        shutil.copytree(root / '.lake', scratch / '.lake')
        baseline = build(scratch)
        if baseline.returncode:
            raise RuntimeError('baseline failed:\n' + baseline.stdout)
        for label, fragment, old, new, theorem in variants:
            before, body = originals[source].split('def build_bl_tree (', 1)
            body, after = body.split('/-- `local void send_all_trees', 1)
            if body.count(old) != 1:
                raise RuntimeError('ambiguous actual mutation: ' + label)
            (scratch / source).write_text(before + 'def build_bl_tree (' + body.replace(old, new) +
                                         '/-- `local void send_all_trees' + after)
            before, body = originals[proof].split('def ' + fragment + ' ', 1)
            body, after = body.split('\n\n', 1)
            if body.count(old) != 1:
                raise RuntimeError('ambiguous named mutation: ' + label)
            changed = before + 'def ' + fragment + ' ' + body.replace(old, new) + '\n\n' + after
            changed = changed.replace('namespace Zlib.Trees.Proofs',
                                      'set_option maxHeartbeats 2000000\n\nnamespace Zlib.Trees.Proofs', 1)
            (scratch / proof).write_text(changed)
            start_offset = changed.index('theorem ' + theorem)
            end_offset = changed.find('\n/--', start_offset)
            start = changed[:start_offset].count('\n') + 1
            end = changed[:end_offset].count('\n') + 1
            result = build(scratch)
            first = re.search(r'^error: ([^\n]+)', result.stdout, re.MULTILINE)
            hit = re.match(re.escape(str(proof)) + r':(\d+):', first.group(1)) if first else None
            exhausted = first and any(x in first.group(1) for x in ('timeout', 'heartbeats', 'recursion depth'))
            if result.returncode == 0 or hit is None or not start <= int(hit.group(1)) < end or exhausted:
                raise RuntimeError('mutant survived or failed outside its actual execution proof:\n' + result.stdout)
            header = changed.split('/-- Literal and distance data needed', 1)[0]
            (scratch / proof).write_text(header + '\nend Zlib.Trees.Proofs\n')
            checked = build(scratch, equality=True)
            if checked.returncode:
                raise RuntimeError('synchronized full source equality failed:\n' + checked.stdout)
            print('KILLED ' + label + ': ' + first.group(1) + '; build_bl_tree_eq still checks', flush=True)


if __name__ == '__main__':
    main()
