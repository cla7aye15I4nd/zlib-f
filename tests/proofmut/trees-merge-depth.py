#!/usr/bin/env python3
"""Reject a dropped parent-depth increment, preserving whole-source decomposition.

The actual translation and its named source fragments are changed together.
The complete build_tree equality must still check. Its depth execution
proof must then fail with a type error, not resource exhaustion.
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
    leaves = Path('ZlibF/Proof/trees.c.build.leaves.lean')
    order = Path('ZlibF/Proof/trees.c.build.order.lean')
    merge = Path('ZlibF/Proof/trees.c.build.merge.lean')
    originals = {p: (root / p).read_text() for p in (source, leaves, order, merge)}
    tail = (root / 'ZlibF/Proof/trees.c.build.tail.lean').read_text()
    old = 'setAt dp node.toInt (mx + 1)'
    new = 'setAt dp node.toInt mx'
    env = os.environ.copy()
    env['LC_ALL'] = 'C'

    def run(where, args):
        return subprocess.run(args, cwd=where, env=env, text=True,
                              stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=180)

    def require_success(result, label):
        if result.returncode:
            raise RuntimeError(label + ':\n' + result.stdout)

    with tempfile.TemporaryDirectory(prefix='trees-depth-parent-') as name:
        scratch = Path(name)
        for file in ('lakefile.toml', 'lean-toolchain'):
            shutil.copy2(root / file, scratch / file)
        shutil.copytree(root / 'ZlibF', scratch / 'ZlibF')
        shutil.copytree(root / '.lake', scratch / '.lake')
        build = ['lake', 'build', 'ZlibF.Proof.«deflate.c.engine.tree-weight»']
        require_success(run(scratch, build), 'baseline bridge build failed')
        print('baseline: complete ledger-to-merge/value proof checks', flush=True)

        changed = {}
        for file, text in originals.items():
            if text.count(old) != 1:
                raise RuntimeError('ambiguous parent-frequency mutation in ' + str(file))
            changed[file] = text.replace(old, new)
            (scratch / file).write_text(changed[file])

        # Keep only source fragments, before any merge execution proof.
        prefix = changed[merge].split('/-- The actual removal followed', 1)[0]
        suffix = tail.split('/-- The actual ordered leaf prefix', 1)[1]
        suffix = '/-- The actual ordered leaf prefix' + suffix
        suffix = suffix.split('/-- The actual descriptor/reset/scan/repair/heapify prefix', 1)[0]
        cutpoint = ('import ZlibF.Proof.«trees.c.build.order»\n' + prefix + suffix
                    + '\nend Zlib.Trees.Proofs\n')
        (scratch / 'DepthParentCutpoint.lean').write_text(cutpoint)
        require_success(run(scratch, ['lake', 'build', 'ZlibF.Proof.«trees.c.build.order»']),
                        'synchronized source-prefix equalities failed')
        require_success(run(scratch, ['lake', 'env', 'lean', 'DepthParentCutpoint.lean']),
                        'synchronized whole-source equality failed')
        print('mutant: complete build_tree source equality still checks', flush=True)

        result = run(scratch, build)
        first = re.search(r'^error: ([^\n]+)', result.stdout, re.MULTILINE)
        hit = re.match(re.escape(str(merge)) + r':(\d+):', first.group(1)) if first else None
        start = changed[merge][:changed[merge].index('theorem ws_btSetDepth')].count('\n') + 1
        end = changed[merge][:changed[merge].index('theorem btParentState')].count('\n') + 1
        exhausted = any(word in result.stdout.lower() for word in
                        ('maximum recursion depth', 'maximum number of heartbeats',
                         'deterministic timeout', 'interrupted', 'out of memory'))
        if (result.returncode == 0 or hit is None or not start <= int(hit.group(1)) < end
                or exhausted or not any(kind in result.stdout for kind in ('Type mismatch', 'unsolved goals', 'Tactic `rfl` failed'))):
            raise RuntimeError('mutant survived or lacked a local type rejection:\n' + result.stdout)
        print('KILLED dropped-parent-depth-increment: ' + first.group(1)
              + '; whole-source equality checks; no resource timeout', flush=True)


if __name__ == '__main__':
    main()
