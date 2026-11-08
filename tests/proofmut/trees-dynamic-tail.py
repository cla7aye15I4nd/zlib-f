#!/usr/bin/env python3
"""Actual dynamic block composition rejects missing reset and wrong final alignment."""
from pathlib import Path
import os
import re
import shutil
import subprocess
import tempfile


def main():
    root = Path(__file__).resolve().parents[2]
    source = Path('ZlibF/Zlib/trees.c.lean')
    cut = Path('ZlibF/Proof/trees.c.flush-source.lean')
    proof = Path('ZlibF/Proof/' + os.environ.get('ZLIBF_TAIL_PROOF',
        'deflate.c.engine.dynamic-block') + '.lean')
    originals = {p: (root / p).read_text() for p in (source, cut)}
    variants = (
        ('dropped-reset', 'init_block s', 'pure ()'),
        ('reversed-final-gate', 'if last != 0 then bi_windup s', 'if last == 0 then bi_windup s'),
    )
    env = os.environ.copy()
    env['LC_ALL'] = 'C'

    def build(where, target):
        return subprocess.run(['lake', 'build', target], cwd=where, env=env, text=True,
                              stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=600)

    with tempfile.TemporaryDirectory(prefix='trees-dynamic-tail-') as name:
        scratch = Path(name)
        for filename in ('lakefile.toml', 'lean-toolchain'):
            shutil.copy2(root / filename, scratch / filename)
        shutil.copytree(root / 'ZlibF', scratch / 'ZlibF')
        shutil.copytree(root / '.lake', scratch / '.lake')
        target = env.get('ZLIBF_TAIL_CALLER', 'ZlibF.Proof.«deflate.c.engine.dynamic-block»')
        baseline = build(scratch, target)
        if baseline.returncode:
            raise RuntimeError('baseline failed:\n' + baseline.stdout)
        print('baseline: actual dynamic construction, body semantics, reset and both block flags check', flush=True)
        text = (root / proof).read_text()
        start = text[:text.index('theorem ' + env.get('ZLIBF_TAIL_THEOREM', 'dynamic_prepared_block_ready'))].count('\n') + 1
        end = text[:text.index('\nend Zlib.Deflate.Engine.Proofs')].count('\n') + 1
        for label, old, new in variants:
            left, body = originals[source].split('def «_tr_flush_block» (', 1)
            body, right = body.split('/-- `int ZLIB_INTERNAL _tr_tally', 1)
            if body.count(old) != 1 or originals[cut].count(old) != 1:
                raise RuntimeError('ambiguous synchronized mutation: ' + label)
            (scratch / source).write_text(left + 'def «_tr_flush_block» (' + body.replace(old, new)
                                         + '/-- `int ZLIB_INTERNAL _tr_tally' + right)
            (scratch / cut).write_text(originals[cut].replace(old, new))
            equality = build(scratch, 'ZlibF.Proof.«trees.c.flush-source»')
            if equality.returncode:
                raise RuntimeError('synchronized complete source equality failed:\n' + equality.stdout)
            result = build(scratch, target)
            first = re.search(r'^error: ([^\n]+)', result.stdout, re.MULTILINE)
            hit = re.match(re.escape(str(proof)) + r':(\d+):', first.group(1)) if first else None
            exhausted = any(word in result.stdout.lower() for word in
                            ('maximum recursion depth', 'maximum number of heartbeats',
                             'deterministic timeout', 'out of memory', 'interrupted'))
            if result.returncode == 0 or hit is None or not start <= int(hit.group(1)) < end or exhausted:
                raise RuntimeError('mutant survived or failed outside dynamic tail execution:\n' + result.stdout)
            print('KILLED ' + label + ': ' + first.group(1)
                  + '; complete flush source equality still checks; no resource failure', flush=True)


if __name__ == '__main__':
    main()
