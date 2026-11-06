#!/usr/bin/env python3
"""Actual scan_tree execution rejects synchronized frequency and loop mutants."""
from pathlib import Path
import os
import re
import shutil
import subprocess
import tempfile


def main():
    root = Path(__file__).resolve().parents[2]
    source = Path('ZlibF/Zlib/trees.c.lean')
    proof = Path('ZlibF/Proof/trees.c.scan-tree.lean')
    originals = {p: (root / p).read_text() for p in (source, proof)}
    variants = (
        ('lost-direct-repeat-count', 'scCounts',
         '((← getFc blt curlen.toInt) + i2us count)',
         '((← getFc blt curlen.toInt) + 1)', 'ws_scCounts'),
        ('wrong-repeat-symbol', 'scCounts',
         'setFc blt REP_3_6.toInt ((← getFc blt REP_3_6.toInt) + 1)',
         'setFc blt REPZ_3_10.toInt ((← getFc blt REPZ_3_10.toInt) + 1)', 'ws_scCounts'),
        ('wrong-zero-run-boundary', 'scCounts',
         'count.toInt ≤ 10', 'count.toInt ≤ 9', 'ws_scCounts'),
        ('extra-continue', 'scBody',
         'count.toInt < max_count.toInt ∧ curlen == nextlen',
         'count.toInt ≤ max_count.toInt ∧ curlen == nextlen', 'ws_scBody'),
        ('skipped-last-symbol', 'scLoop',
         'n.toInt ≤ mc.toInt', 'n.toInt < mc.toInt', 'ws_scLoop'),
    )
    env = os.environ.copy()
    env['LC_ALL'] = 'C'

    def build(where, equality=False):
        target = 'ZlibF.Proof.«trees.c.scan-tree»' if equality else 'ZlibF.Proof.«trees.c.bl-support»'
        return subprocess.run(['lake', 'build', target],
                              cwd=where, env=env, text=True, stdout=subprocess.PIPE,
                              stderr=subprocess.STDOUT, timeout=600)

    with tempfile.TemporaryDirectory(prefix='trees-scan-tree-') as name:
        scratch = Path(name)
        for f in ('lakefile.toml', 'lean-toolchain'):
            shutil.copy2(root / f, scratch / f)
        shutil.copytree(root / 'ZlibF', scratch / 'ZlibF')
        shutil.copytree(root / '.lake', scratch / '.lake')
        baseline = build(scratch)
        if baseline.returncode:
            raise RuntimeError('baseline failed:\n' + baseline.stdout)
        for label, fragment, old, new, theorem in variants:
            before, body = originals[source].split('def scan_tree (', 1)
            body, after = body.split('/-- `local void send_tree', 1)
            source_old = old.replace('mc.toInt', 'max_code.toInt')
            source_new = new.replace('mc.toInt', 'max_code.toInt')
            if body.count(source_old) != 1:
                raise RuntimeError('ambiguous actual mutation: ' + label)
            (scratch / source).write_text(before + 'def scan_tree (' + body.replace(source_old, source_new) +
                                         '/-- `local void send_tree' + after)
            before, body = originals[proof].split('def ' + fragment + ' ', 1)
            body, after = body.split('\n\n/--', 1)
            if body.count(old) != 1:
                raise RuntimeError('ambiguous named mutation: ' + label)
            changed = before + 'def ' + fragment + ' ' + body.replace(old, new) + '\n\n/--' + after
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
            # Retain only source definitions and the independent whole-call equality.
            header = changed.split('/-- Array effects of a finished run.', 1)[0]
            (scratch / proof).write_text(header + '\nend Zlib.Trees.Proofs\n')
            checked = build(scratch, equality=True)
            if checked.returncode:
                raise RuntimeError('synchronized full source equality failed:\n' + checked.stdout)
            print('KILLED ' + label + ': ' + first.group(1) + '; scan_tree_eq still checks', flush=True)


if __name__ == '__main__':
    main()
