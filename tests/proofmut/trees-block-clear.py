#!/usr/bin/env python3
"""Actual block-clear mutations must fail the directly unfolded init_block proof."""
from pathlib import Path
import os
import re
import shutil
import subprocess
import tempfile


def main():
    root = Path(__file__).resolve().parents[2]
    source = Path('ZlibF/Zlib/trees.c.lean')
    proof = Path('ZlibF/Proof/trees.c.block.lean')
    original = (root / source).read_text()
    variants = (
        ('nonzero-bl-frequency', 'setFc (← pBltree s) n.toInt 0', 'setFc (← pBltree s) n.toInt 1'),
        ('nonzero-dynamic-cost', '{ d with opt_len := 0 }', '{ d with opt_len := 1 }'),
        ('nonzero-fixed-cost', '{ d with static_len := 0 }', '{ d with static_len := 1 }'),
    )
    env = os.environ.copy()
    env['LC_ALL'] = 'C'

    def build(where, target):
        return subprocess.run(['lake', 'build', target], cwd=where, env=env, text=True,
                              stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=180)

    with tempfile.TemporaryDirectory(prefix='trees-block-clear-') as name:
        scratch = Path(name)
        for filename in ('lakefile.toml', 'lean-toolchain'):
            shutil.copy2(root / filename, scratch / filename)
        shutil.copytree(root / 'ZlibF', scratch / 'ZlibF')
        shutil.copytree(root / '.lake', scratch / '.lake')
        baseline = build(scratch, 'ZlibF.Proof.«deflate.c.engine.dynamic-header»')
        if baseline.returncode:
            raise RuntimeError('baseline failed:\n' + baseline.stdout)
        print('baseline: default init/reset zeros and actual dynamic header check', flush=True)
        text = (root / proof).read_text()
        start = text[:text.index('theorem init_block_spec0')].count('\n') + 1
        end = text[:text.index('def trInitRec')].count('\n') + 1
        for label, old, new in variants:
            left, body = original.split('def init_block (', 1)
            body, right = body.split('/-- `void ZLIB_INTERNAL _tr_init', 1)
            if body.count(old) != 1:
                raise RuntimeError('ambiguous actual mutation: ' + label)
            (scratch / source).write_text(left + 'def init_block (' + body.replace(old, new)
                                         + '/-- `void ZLIB_INTERNAL _tr_init' + right)
            result = build(scratch, 'ZlibF.Proof.«trees.c.initial-clear»')
            first = re.search(r'^error: ([^\n]+)', result.stdout, re.MULTILINE)
            hit = re.match(re.escape(str(proof)) + r':(\d+):', first.group(1)) if first else None
            exhausted = any(word in result.stdout.lower() for word in
                            ('maximum recursion depth', 'maximum number of heartbeats',
                             'deterministic timeout', 'out of memory', 'interrupted'))
            if result.returncode == 0 or hit is None or not start <= int(hit.group(1)) < end or exhausted:
                raise RuntimeError('mutant survived or failed outside init_block execution:\n' + result.stdout)
            print('KILLED ' + label + ': ' + first.group(1)
                  + '; actual init_block unfolded directly; no resource failure', flush=True)


if __name__ == '__main__':
    main()
