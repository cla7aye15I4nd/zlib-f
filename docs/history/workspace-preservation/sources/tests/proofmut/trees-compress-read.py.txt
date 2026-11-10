#!/usr/bin/env python3
"""Actual compress_block read mutants fail the checked read-sequence proof.

This does not claim a complete compress_block proof. The synchronized whole
source equality is checked independently of the rejected execution proof.
"""
from pathlib import Path
import os
import re
import shutil
import subprocess
import tempfile


def main():
    root = Path(__file__).resolve().parents[2]
    source = Path('ZlibF/Zlib/trees.c.lean')
    proof = Path('ZlibF/Proof/trees.c.compress-source.lean')
    originals = {p: (root / p).read_text() for p in (source, proof)}
    variants = (
        ('skip-first-cursor-byte',
         'let b0 ← Ptr.index sb sx.toNat\n        let sx := sx + 1',
         'let b0 ← Ptr.index sb sx.toNat\n        let sx := sx + 2',
         'let b0 ← Ptr.index sb sx.toNat\n  let sx := sx + 1',
         'let b0 ← Ptr.index sb sx.toNat\n  let sx := sx + 2'),
        ('wrong-distance-byte-shift',
         '((b1.toUInt32 &&& 0xff) <<< 8)', '((b1.toUInt32 &&& 0xff) <<< 7)',
         '((b1.toUInt32 &&& 0xff) <<< 8)', '((b1.toUInt32 &&& 0xff) <<< 7)'),
        ('wrong-third-byte-offset',
         'let b2 ← Ptr.index sb sx.toNat', 'let b2 ← Ptr.index sb (sx.toNat + 1)',
         'let b2 ← Ptr.index sb sx.toNat', 'let b2 ← Ptr.index sb (sx.toNat + 1)'),
        ('drop-final-cursor-increment',
         'let b2 ← Ptr.index sb sx.toNat\n        let sx := sx + 1',
         'let b2 ← Ptr.index sb sx.toNat\n        let sx := sx',
         'let b2 ← Ptr.index sb sx.toNat\n  let sx := sx + 1',
         'let b2 ← Ptr.index sb sx.toNat\n  let sx := sx'),
    )
    env = os.environ.copy()
    env['LC_ALL'] = 'C'

    def run(where, args):
        return subprocess.run(args, cwd=where, env=env, text=True,
                              stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=600)

    def build(where):
        return run(where, ['lake', 'build', 'ZlibF.Proof.«trees.c.compress-source»'])

    with tempfile.TemporaryDirectory(prefix='trees-compress-read-') as name:
        scratch = Path(name)
        for file in ('lakefile.toml', 'lean-toolchain'):
            shutil.copy2(root / file, scratch / file)
        shutil.copytree(root / 'ZlibF', scratch / 'ZlibF')
        shutil.copytree(root / '.lake', scratch / '.lake')
        baseline = build(scratch)
        if baseline.returncode:
            raise RuntimeError('baseline failed:\n' + baseline.stdout)
        print('baseline: actual read sequence and independent whole source equality check', flush=True)
        for label, src_old, src_new, old, new in variants:
            left, body = originals[source].split('def compress_block (', 1)
            body, right = body.split('/-- `local int detect_data_type', 1)
            if body.count(src_old) != 1:
                raise RuntimeError('ambiguous actual mutation: ' + label)
            (scratch / source).write_text(left + 'def compress_block (' + body.replace(src_old, src_new)
                                         + '/-- `local int detect_data_type' + right)
            left, body = originals[proof].split('def cbReadSymbol ', 1)
            body, right = body.split('/-- The actual body groups', 1)
            if body.count(old) != 1:
                raise RuntimeError('ambiguous named mutation: ' + label)
            changed = left + 'def cbReadSymbol ' + body.replace(old, new) + '/-- The actual body groups' + right
            (scratch / proof).write_text(changed)
            start = changed[:changed.index('theorem cbReadSymbol_run')].count('\n') + 1
            result = build(scratch)
            first = re.search(r'^error: ([^\n]+)', result.stdout, re.MULTILINE)
            hit = re.match(re.escape(str(proof)) + r':(\d+):', first.group(1)) if first else None
            exhausted = any(word in result.stdout.lower()
                            for word in ('maximum recursion depth', 'maximum number of heartbeats',
                                         'deterministic timeout'))
            if result.returncode == 0 or hit is None or int(hit.group(1)) < start or exhausted:
                raise RuntimeError('mutant survived or failed outside its read execution proof:\n' + result.stdout)
            prefix = changed.split('/-- The two loaded bytes reconstruct', 1)[0]
            (scratch / 'CompressReadCutpoint.lean').write_text(prefix + '\nend Zlib.Trees.Proofs\n')
            checked = run(scratch, ['lake', 'env', 'lean', 'CompressReadCutpoint.lean'])
            if checked.returncode:
                raise RuntimeError('independent synchronized whole source equality failed:\n' + checked.stdout)
            print('KILLED ' + label + ': ' + first.group(1) + '; compress_block_eq still checks', flush=True)


if __name__ == '__main__':
    main()
