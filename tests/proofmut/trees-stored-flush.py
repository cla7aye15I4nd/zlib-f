#!/usr/bin/env python3
"""The complete stored flush rejects source comparison, writer and tail mutations."""
from pathlib import Path
import os
import re
import shutil
import subprocess
import sys
import tempfile


def main():
    root = Path(__file__).resolve().parents[2]
    directory = root / 'tests/proofmut'
    env = os.environ.copy()
    env['LC_ALL'] = 'C'
    env['ZLIBF_STORED_CALLER'] = 'deflate.c.engine.flush-stored'
    env['ZLIBF_TAIL_CALLER'] = 'ZlibF.Proof.«deflate.c.engine.flush-stored»'
    env['ZLIBF_TAIL_PROOF'] = 'deflate.c.engine.stored-block'
    env['ZLIBF_TAIL_THEOREM'] = 'stored_block_ready'
    for name in ('trees-stored-block.py', 'trees-dynamic-tail.py'):
        subprocess.run([sys.executable, str(directory / name)], env=env, check=True)
    paths = [Path('ZlibF/Zlib/trees.c.lean'), Path('ZlibF/Proof/trees.c.flush-source.lean'),
             Path('ZlibF/Proof/trees.c.dynamic-header.lean'),
             Path('ZlibF/Proof/deflate.c.engine.block-prepare.lean')]
    proof = Path('ZlibF/Proof/deflate.c.engine.flush-stored.lean')
    old = 'stored_len + 4 ≤ opt_lenb'
    new = 'stored_len + 5 ≤ opt_lenb'

    def build(where, module):
        return subprocess.run(['lake', 'build', 'ZlibF.Proof.«' + module + '»'], cwd=where,
                              env=env, text=True, stdout=subprocess.PIPE,
                              stderr=subprocess.STDOUT, timeout=180)

    def success(result, label):
        if result.returncode:
            raise RuntimeError(label + ':\n' + result.stdout)

    with tempfile.TemporaryDirectory(prefix='trees-stored-selection-') as name:
        scratch = Path(name)
        for filename in ('lakefile.toml', 'lean-toolchain'):
            shutil.copy2(root / filename, scratch / filename)
        shutil.copytree(root / 'ZlibF', scratch / 'ZlibF')
        shutil.copytree(root / '.lake', scratch / '.lake')
        success(build(scratch, 'deflate.c.engine.flush-stored'), 'positive complete flush')
        for path in paths:
            text = (root / path).read_text()
            if text.count(old) != 1:
                raise RuntimeError('ambiguous stored selection comparison: ' + str(path))
            (scratch / path).write_text(text.replace(old, new))
        for module in ('trees.c.flush-source', 'deflate.c.engine.block-prepare'):
            success(build(scratch, module), 'synchronized complete source equality')
        text = (root / proof).read_text()
        start = text[:text.index('theorem flush_stored_dispatch')].count('\n') + 1
        end = text[:text.index('theorem flush_stored_prepared')].count('\n') + 1
        result = build(scratch, 'deflate.c.engine.flush-stored')
        first = re.search(r'^error: ([^\n]+)', result.stdout, re.MULTILINE)
        hit = re.match(re.escape(str(proof)) + r':(\d+):', first.group(1)) if first else None
        exhausted = any(word in result.stdout.lower() for word in
                        ('maximum recursion depth', 'maximum number of heartbeats',
                         'deterministic timeout', 'interrupted', 'out of memory'))
        if result.returncode == 0 or hit is None or not start <= int(hit.group(1)) < end or exhausted:
            raise RuntimeError('stored comparison survived or failed outside dispatch proof:\n' + result.stdout)
        print('KILLED stored-cost-threshold: ' + first.group(1)
              + '; whole flush and preparation source equalities check; no resource failure', flush=True)


if __name__ == '__main__':
    main()
