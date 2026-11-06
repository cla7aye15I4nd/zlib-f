#!/usr/bin/env python3
"""Actual send_tree must reject synchronized branch and loop mutations."""
from pathlib import Path
import os
import re
import shutil
import subprocess
import tempfile


def main():
    root = Path(__file__).resolve().parents[2]
    source = Path('ZlibF/Zlib/trees.c.lean')
    proof = Path('ZlibF/Proof/trees.c.send-tree.lean')
    originals = {p: (root / p).read_text() for p in (source, proof)}
    variants = (
        ('doubled-repeat-decrement', 'stRepeat', 'isub c 1', 'isub c 2',
         'stRepeat_run', 'theorem stCode_extra'),
        ('wrong-repeat-extra-width', 'stSend',
         'send_bits s (← isub count 3) 2', 'send_bits s (← isub count 3) 3',
         'stSend_run', 'theorem emitState_tk_arr'),
        ('lost-first-code-decrement', 'stSend', 'count ← isub count 1\n', 'count ← pure count\n',
         'stSend_run', 'theorem emitState_tk_arr'),
        ('wrong-zero-run-boundary', 'stSend', 'count.toInt ≤ 10', 'count.toInt ≤ 9',
         'stSend_run', 'theorem emitState_tk_arr'),
        ('wrong-long-run-base', 'stSend', 'isub count 11', 'isub count 10',
         'stSend_run', 'theorem emitState_tk_arr'),
        ('extra-continue', 'stBody',
         'count.toInt < max_count.toInt ∧ curlen == nextlen',
         'count.toInt ≤ max_count.toInt ∧ curlen == nextlen',
         'stBody_run', 'theorem st_scanFreq_mono'),
        ('skipped-last-symbol', 'stLoop', 'n.toInt ≤ mc.toInt', 'n.toInt < mc.toInt',
         'stLoop_run', 'theorem send_tree_emit'),
        ('wrong-next-length', 'stBody', 'getDl tree (← iadd n 1).toInt', 'getDl tree (← iadd n 2).toInt',
         'stBody_run', 'theorem st_scanFreq_mono'),
    )
    env = os.environ.copy()
    env['LC_ALL'] = 'C'

    def run(where, args):
        return subprocess.run(args, cwd=where, env=env, text=True,
                              stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=600)

    def build(where):
        return run(where, ['lake', 'build', 'ZlibF.Proof.«trees.c.send-tree»'])

    with tempfile.TemporaryDirectory(prefix='trees-send-tree-') as name:
        scratch = Path(name)
        for file in ('lakefile.toml', 'lean-toolchain'):
            shutil.copy2(root / file, scratch / file)
        shutil.copytree(root / 'ZlibF', scratch / 'ZlibF')
        shutil.copytree(root / '.lake', scratch / '.lake')
        baseline = build(scratch)
        if baseline.returncode:
            raise RuntimeError('baseline failed:\n' + baseline.stdout)
        print('baseline: complete actual send_tree emission checks', flush=True)
        for label, fragment, old, new, theorem, end_marker in variants:
            left, body = originals[source].split('def send_tree (', 1)
            body, right = body.split('/-- `local int build_bl_tree', 1)
            src_old = old.replace('mc.toInt', 'max_code.toInt')
            src_new = new.replace('mc.toInt', 'max_code.toInt')
            if body.count(src_old) != 1:
                raise RuntimeError('ambiguous actual mutation: ' + label)
            (scratch / source).write_text(left + 'def send_tree (' + body.replace(src_old, src_new)
                                         + '/-- `local int build_bl_tree' + right)
            left, body = originals[proof].split('def ' + fragment + ' ', 1)
            body, right = body.split('\n\n', 1)
            if body.count(old) != 1:
                raise RuntimeError('ambiguous named mutation: ' + label)
            changed = left + 'def ' + fragment + ' ' + body.replace(old, new) + '\n\n' + right
            (scratch / proof).write_text(changed)
            start = changed[:changed.index('theorem ' + theorem)].count('\n') + 1
            end = changed[:changed.index(end_marker)].count('\n') + 1
            result = build(scratch)
            first = re.search(r'^error: ([^\n]+)', result.stdout, re.MULTILINE)
            hit = re.match(re.escape(str(proof)) + r':(\d+):', first.group(1)) if first else None
            exhausted = any(word in result.stdout.lower()
                            for word in ('maximum recursion depth', 'maximum number of heartbeats',
                                         'deterministic timeout'))
            if result.returncode == 0 or hit is None or not start <= int(hit.group(1)) < end or exhausted:
                raise RuntimeError('mutant survived or failed outside its execution proof:\n' + result.stdout)
            header = changed.split('/-- Scalar checked arithmetic used', 1)[0]
            (scratch / 'SendTreeCutpoint.lean').write_text(header + '\nend Zlib.Trees.Proofs\n')
            checked = run(scratch, ['lake', 'env', 'lean', 'SendTreeCutpoint.lean'])
            if checked.returncode:
                raise RuntimeError('synchronized complete source equality failed:\n' + checked.stdout)
            print('KILLED ' + label + ': ' + first.group(1) + '; send_tree_eq still checks', flush=True)


if __name__ == '__main__':
    main()
