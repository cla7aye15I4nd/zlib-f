#!/usr/bin/env python3
"""Real static-cost mutations must fail the matching execution or balance proof."""
from pathlib import Path
import os
import re
import shutil
import subprocess
import tempfile


def main():
    root = Path(__file__).resolve().parents[2]
    paths = [Path('ZlibF/Zlib/trees.c.lean'),
             Path('ZlibF/Proof/trees.c.build.force.lean'),
             Path('ZlibF/Proof/trees.c.heap.gbdef.lean')]
    originals = {p: (root / p).read_text() for p in paths}
    env = os.environ.copy()
    env['LC_ALL'] = 'C'

    def build(where, target):
        return subprocess.run(['lake', 'build', target], cwd=where, env=env, text=True,
                              stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=180)

    def success(result, label):
        if result.returncode:
            raise RuntimeError(label + ':\n' + result.stdout)

    variants = (
        ('dropped-dummy-static-deduction', 'trees.c.build.leaves', 'trees.c.build.static-force',
         'BTLeafInv.force_static_balance', 'forceNode_le_two'),
        ('dropped-static-leaf-contribution', 'trees.c.heap.gbdef', 'trees.c.heap.gbp1',
         'ws_gbTail2_ref', 'ws_index_static'),
    )
    with tempfile.TemporaryDirectory(prefix='trees-static-cost-') as name:
        scratch = Path(name)
        for filename in ('lakefile.toml', 'lean-toolchain'):
            shutil.copy2(root / filename, scratch / filename)
        shutil.copytree(root / 'ZlibF', scratch / 'ZlibF')
        shutil.copytree(root / '.lake', scratch / '.lake')
        success(build(scratch, 'ZlibF.Proof.«deflate.c.engine.stored-length»'), 'positive caller')
        print('baseline: complete constructed static cost and stored-position room check', flush=True)
        for label, gate, module, first_name, last_name in variants:
            for path, original in originals.items():
                text = original
                if label.startswith('dropped-dummy'):
                    if path in paths[:2]:
                        old = 'd.static_len - l.toUInt64'
                        if old not in text:
                            raise RuntimeError('missing actual dummy subtraction')
                        text = text.replace(old, 'd.static_len - (0 : UInt64)')
                    if path == paths[1]:
                        old = 'd.static_len - (f node.toInt.toNat).toUInt64'
                        if text.count(old) != 1:
                            raise RuntimeError('ambiguous force-state effect')
                        text = text.replace(old, 'd.static_len - (0 : UInt64)')
                        text = text.replace('S - (f node.toInt.toNat).toUInt64', 'S - (0 : UInt64)')
                elif path in (paths[0], paths[2]):
                    old = 'd.static_len + f.toUInt64 * (i2u t2).toUInt64'
                    if text.count(old) != 1:
                        raise RuntimeError('ambiguous static accumulation')
                    text = text.replace(old, 'd.static_len + (0 : UInt64)')
                (scratch / path).write_text(text)
            success(build(scratch, 'ZlibF.Proof.«' + gate + '»'), label + ' complete source equality')
            proof = Path('ZlibF/Proof/' + module + '.lean')
            text = (root / proof).read_text()
            start = text[:text.index('theorem ' + first_name)].count('\n') + 1
            end = text[:text.index('theorem ' + last_name)].count('\n') + 1
            result = build(scratch, 'ZlibF.Proof.«' + module + '»')
            first = re.search(r'^error: ([^\n]+)', result.stdout, re.MULTILINE)
            hit = re.match(re.escape(str(proof)) + r':(\d+):', first.group(1)) if first else None
            exhausted = any(word in result.stdout.lower() for word in
                            ('maximum recursion depth', 'maximum number of heartbeats',
                             'deterministic timeout', 'interrupted', 'out of memory'))
            if result.returncode == 0 or hit is None or not start <= int(hit.group(1)) < end or exhausted:
                raise RuntimeError(label + ' survived or failed outside its proof:\n' + result.stdout)
            print('KILLED ' + label + ': ' + first.group(1)
                  + '; complete synchronized source equality checks; no resource failure', flush=True)


if __name__ == '__main__':
    main()
