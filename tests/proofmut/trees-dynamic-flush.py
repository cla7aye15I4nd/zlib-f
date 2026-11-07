#!/usr/bin/env python3
"""Complete dynamic flush rejects wrong actual cost and branch comparisons."""
from pathlib import Path
import os
import re
import shutil
import subprocess
import tempfile


def main():
    root = Path(__file__).resolve().parents[2]
    proof = Path('ZlibF/Proof/deflate.c.engine.flush-dynamic.lean')
    paths = [Path('ZlibF/Zlib/trees.c.lean'), Path('ZlibF/Proof/trees.c.flush-source.lean'),
             Path('ZlibF/Proof/trees.c.dynamic-header.lean'),
             Path('ZlibF/Proof/deflate.c.engine.block-prepare.lean'), proof]
    originals = {p: (root / p).read_text() for p in paths}
    variants = (
        ('reversed-static-cost-preference', 'if static_lenb ≤ opt_lenb ∨', 'if opt_lenb ≤ static_lenb ∨'),
        ('reversed-fixed-branch-test', 'else if static_lenb == opt_lenb then', 'else if static_lenb != opt_lenb then'),
    )
    env = os.environ.copy()
    env['LC_ALL'] = 'C'

    def build(where, *modules):
        return subprocess.run(['lake', 'build'] + ['ZlibF.Proof.«' + m + '»' for m in modules],
                              cwd=where, env=env, text=True, stdout=subprocess.PIPE,
                              stderr=subprocess.STDOUT, timeout=600)

    def success(result, label):
        if result.returncode:
            raise RuntimeError(label + ':\n' + result.stdout)

    with tempfile.TemporaryDirectory(prefix='trees-dynamic-selection-') as name:
        scratch = Path(name)
        for filename in ('lakefile.toml', 'lean-toolchain'):
            shutil.copy2(root / filename, scratch / filename)
        shutil.copytree(root / 'ZlibF', scratch / 'ZlibF')
        shutil.copytree(root / '.lake', scratch / '.lake')
        success(build(scratch, 'deflate.c.engine.flush-dynamic', 'deflate.c.engine.fixed-clear'),
                'positive full dynamic flush and fixed clear execution')
        print('baseline: actual dynamic selection/preparation/output and fixed clear check', flush=True)
        for label, old, new in variants:
            for path, original in originals.items():
                if original.count(old) != 1:
                    raise RuntimeError('ambiguous actual branch mutation: ' + str(path))
                (scratch / path).write_text(original.replace(old, new))
            changed = (scratch / proof).read_text()
            marker = '/-- If the actual rounded costs'
            (scratch / proof).write_text(changed.split(marker, 1)[0] + '\nend Zlib.Deflate.Engine.Proofs\n')
            success(build(scratch, 'deflate.c.engine.flush-dynamic'), label + ' whole source equality')
            (scratch / proof).write_text(changed)
            start = changed[:changed.index('theorem flush_dynamic_dispatch')].count('\n') + 1
            end = changed[:changed.index('theorem flush_dynamic_prepared')].count('\n') + 1
            result = build(scratch, 'deflate.c.engine.flush-dynamic')
            first = re.search(r'^error: ([^\n]+)', result.stdout, re.MULTILINE)
            hit = re.match(re.escape(str(proof)) + r':(\d+):', first.group(1)) if first else None
            exhausted = any(word in result.stdout.lower() for word in
                            ('maximum recursion depth', 'maximum number of heartbeats',
                             'deterministic timeout', 'interrupted', 'out of memory'))
            if result.returncode == 0 or hit is None or not start <= int(hit.group(1)) < end or exhausted:
                raise RuntimeError(label + ' survived or failed outside dynamic dispatch:\n' + result.stdout)
            print('KILLED ' + label + ': ' + first.group(1)
                  + '; synchronized complete source equality checks; no resource failure', flush=True)


if __name__ == '__main__':
    main()
