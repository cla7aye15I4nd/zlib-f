#!/usr/bin/env python3
"""Actual send_all_trees mutations must fail its execution proofs."""
from pathlib import Path
import os
import re
import shutil
import subprocess
import tempfile


def main():
    root = Path(__file__).resolve().parents[2]
    source = Path('ZlibF/Zlib/trees.c.lean')
    proof = Path('ZlibF/Proof/trees.c.all-trees.lean')
    originals = {p: (root / p).read_text() for p in (source, proof)}
    variants = (
        ('wrong-literal-count-base', 'atCounts',
         'send_bits s (← isub lcodes 257) 5', 'send_bits s (← isub lcodes 256) 5',
         'atField s lcodes 257 5', 'atField s lcodes 256 5',
         'atCounts_run', 'theorem atLengthBody_run'),
        ('wrong-distance-count-width', 'atCounts',
         'send_bits s (← isub dcodes 1) 5', 'send_bits s (← isub dcodes 1) 4',
         'atField s dcodes 1 5', 'atField s dcodes 1 4',
         'atCounts_run', 'theorem atLengthBody_run'),
        ('wrong-bl-count-base', 'atCounts',
         'send_bits s (← isub blcodes 4) 4', 'send_bits s (← isub blcodes 3) 4',
         'atField s blcodes 4 4', 'atField s blcodes 3 4',
         'atCounts_run', 'theorem atLengthBody_run'),
        ('extra-bl-length', 'atLengthLoop',
         'r.toInt < blcodes.toInt', 'r.toInt ≤ blcodes.toInt',
         'r.toInt < blcodes.toInt', 'r.toInt ≤ blcodes.toInt',
         'atLengthLoop_run', 'theorem atTree_run'),
        ('wrong-bl-length-width', 'atLengthBody',
         'send_bits s (u16i l) 3', 'send_bits s (u16i l) 4',
         'send_bits s (u16i l) 3', 'send_bits s (u16i l) 4',
         'atLengthBody_run', 'theorem atLengthIteration_run'),
        ('wrong-permutation-rank', 'atLengthBody',
         'blOrder r.toInt', 'blOrder (r.toInt + 1)',
         'blOrder r.toInt', 'blOrder (r.toInt + 1)',
         'atLengthBody_run', 'theorem atLengthIteration_run'),
        ('dropped-distance-tree', 'atTrees',
         'send_tree s (← pDtree s) (← isub dcodes 1)', 'pure ()',
         'atTree s .dist dcodes', 'pure ()',
         'atTrees_run', 'structure AllTreeData'),
        ('wrong-distance-source', 'atSourcePtr',
         'send_tree s (← pDtree s) (← isub dcodes 1)',
         'send_tree s (← pLtree s) (← isub dcodes 1)',
         '| .dist => pDtree s', '| .dist => pLtree s',
         'atTree_run', 'theorem atTrees_run'),
    )
    env = os.environ.copy()
    env['LC_ALL'] = 'C'

    def run(where, args):
        return subprocess.run(args, cwd=where, env=env, text=True,
                              stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=600)

    def build(where):
        return run(where, ['lake', 'build', 'ZlibF.Proof.«trees.c.all-trees»'])

    with tempfile.TemporaryDirectory(prefix='trees-all-trees-') as name:
        scratch = Path(name)
        for file in ('lakefile.toml', 'lean-toolchain'):
            shutil.copy2(root / file, scratch / file)
        shutil.copytree(root / 'ZlibF', scratch / 'ZlibF')
        shutil.copytree(root / '.lake', scratch / '.lake')
        baseline = build(scratch)
        if baseline.returncode:
            raise RuntimeError('baseline failed:\n' + baseline.stdout)
        print('baseline: complete actual header writer and construction data check', flush=True)
        for label, fragment, src_old, src_new, old, new, theorem, end_marker in variants:
            left, body = originals[source].split('def send_all_trees (', 1)
            body, right = body.split('/-- `void ZLIB_INTERNAL _tr_stored_block', 1)
            if body.count(src_old) != 1:
                raise RuntimeError('ambiguous actual mutation: ' + label)
            (scratch / source).write_text(left + 'def send_all_trees (' + body.replace(src_old, src_new)
                                         + '/-- `void ZLIB_INTERNAL _tr_stored_block' + right)
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
            header = changed.split('/-- A count field emits its exact', 1)[0]
            (scratch / 'AllTreesCutpoint.lean').write_text(header + '\nend Zlib.Trees.Proofs\n')
            checked = run(scratch, ['lake', 'env', 'lean', 'AllTreesCutpoint.lean'])
            if checked.returncode:
                raise RuntimeError('synchronized complete source equality failed:\n' + checked.stdout)
            print('KILLED ' + label + ': ' + first.group(1) + '; send_all_trees_eq still checks', flush=True)


if __name__ == '__main__':
    main()
