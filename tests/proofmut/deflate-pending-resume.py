#!/usr/bin/env python3
"""Reject advanced-cursor flush_pending regressions.

Only errors in this function's execution proof count. Source compilation
must succeed first. Resource failures are inconclusive.
"""
from pathlib import Path
import os
import re
import shutil
import subprocess
import tempfile


def main():
    root = Path(__file__).resolve().parents[2]
    lake = shutil.which('lake') or str(Path.home() / '.elan/bin/lake')
    source = Path('ZlibF/Zlib/deflate_base.c.lean')
    proof = Path('ZlibF/Proof/deflate.c.engine.pending-output.lean')
    original = (root / source).read_text()
    text = (root / proof).read_text()
    module = 'ZlibF.Proof.«deflate.c.engine.pending-resume»'
    cases = (
        ('copy-from-base', 'memcpyB z.next_out d.pending_out len.toNat',
         'memcpyB z.next_out d.pending_buf len.toNat'),
        ('advance-from-base', 'let po ← padd d.pending_out len.toNat',
         'let po ← padd d.pending_buf len.toNat'),
    )
    start = text[:text.index('theorem flush_pending_low_raw')].count('\n') + 1
    end = len(text.splitlines()) + 1
    with tempfile.TemporaryDirectory(prefix='deflate-pending-resume-') as directory:
        scratch = Path(directory)
        for name in ('lakefile.toml', 'lean-toolchain'):
            shutil.copy2(root / name, scratch / name)
        shutil.copytree(root / 'ZlibF', scratch / 'ZlibF')
        shutil.copytree(root / '.lake/build', scratch / '.lake/build')

        def build(target):
            return subprocess.run([lake, 'build', target], cwd=scratch,
                                  env=dict(os.environ, LC_ALL='C'), text=True,
                                  stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=240)

        baseline = build(module)
        if baseline.returncode:
            raise RuntimeError('positive actual pending-copy baseline:\n' + baseline.stdout)
        print('baseline: advanced-cursor execution, arbitrary raw capacities and exact two-call bit concatenation', flush=True)
        for label, old, new in cases:
            before, rest = original.split('def flush_pending (', 1)
            body, after = rest.split('/-- `FLUSH_BLOCK_ONLY(', 1)
            if body.count(old) != 1:
                raise RuntimeError('ambiguous source mutation: ' + label)
            (scratch / source).write_text(before + 'def flush_pending (' + body.replace(old, new)
                                         + '/-- `FLUSH_BLOCK_ONLY(' + after)
            compiled = build('ZlibF.Zlib.«deflate_base.c»')
            if compiled.returncode:
                raise RuntimeError(label + ' source compilation:\n' + compiled.stdout)
            result = build(module)
            error = re.search(r'^error: ([^\n]+)', result.stdout, re.MULTILINE)
            hit = re.match(re.escape(str(proof)) + r':(\d+):', error.group(1)) if error else None
            resource = any(word in result.stdout.lower() for word in (
                'maximum recursion depth', 'maximum number of heartbeats', 'deep recursion detected',
                'deterministic timeout', 'interrupted', 'out of memory'))
            if result.returncode == 0 or hit is None or resource or not start <= int(hit.group(1)) < end:
                raise RuntimeError(label + ' survived or failed inconclusively:\n' + result.stdout)
            print('KILLED ' + label + ': ' + error.group(1), flush=True)


if __name__ == '__main__':
    main()
