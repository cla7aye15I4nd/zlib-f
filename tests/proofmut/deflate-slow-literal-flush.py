#!/usr/bin/env python3
"""The actual full literal decision must flush a nonfinal block."""
from pathlib import Path
import os
import re
import shutil
import subprocess
import tempfile


def main():
    root = Path(__file__).resolve().parents[2]
    lake = shutil.which('lake') or str(Path.home() / '.elan/bin/lake')
    source = Path('ZlibF/Zlib/deflate_strategies.c.lean')
    cut = Path('ZlibF/Proof/deflate.c.engine.slow-source.lean')
    proof = Path('ZlibF/Proof/deflate.c.engine.slow-literal-loop.lean')
    originals = {p: (root / p).read_text() for p in (source, cut, proof)}
    old = 'if bflush then FLUSH_BLOCK_ONLY s 0'
    variants = (
        ('dropped-full-buffer-flush', 'if bflush then pure ()'),
        ('premature-final-block', 'if bflush then FLUSH_BLOCK_ONLY s 1'),
    )
    env = os.environ.copy()
    env['LC_ALL'] = 'C'

    def build(where, target):
        return subprocess.run([lake, 'build', 'ZlibF.Proof.«' + target + '»'],
                              cwd=where, env=env, text=True, stdout=subprocess.PIPE,
                              stderr=subprocess.STDOUT, timeout=600)

    def success(result, label):
        if result.returncode:
            raise RuntimeError(label + ':\n' + result.stdout)

    with tempfile.TemporaryDirectory(prefix='deflate-slow-literal-flush-') as name:
        scratch = Path(name)
        for filename in ('lakefile.toml', 'lean-toolchain'):
            shutil.copy2(root / filename, scratch / filename)
        shutil.copytree(root / 'ZlibF', scratch / 'ZlibF')
        shutil.copytree(root / '.lake/build', scratch / '.lake/build')
        caller = env.get('ZLIBF_LITERAL_FLUSH_CALLER', 'deflate.c.engine.slow-body-literal-flush')
        success(build(scratch, caller), 'positive actual full literal content boundary')
        print('baseline: selected actual full literal caller retains content boundary', flush=True)
        for label, new in variants:
            left, body = originals[source].split('def deflate_slow_body (', 1)
            middle, right = body.split('/-- `local block_state deflate_slow(', 1)
            if middle.count(old) != 1 or originals[cut].count(old) != 1:
                raise RuntimeError('ambiguous full literal flush mutation')
            (scratch / source).write_text(left + 'def deflate_slow_body (' + middle.replace(old, new)
                                         + '/-- `local block_state deflate_slow(' + right)
            (scratch / cut).write_text(originals[cut].replace(old, new))
            success(build(scratch, 'deflate.c.engine.slow-source'), label + ' complete synchronized slow-body source equality')
            result = build(scratch, 'deflate.c.engine.slow-literal-flush')
            first = re.search(r'^error: ([^\n]+)', result.stdout, re.MULTILINE)
            hit = re.match(re.escape(str(proof)) + r':(\d+):', first.group(1)) if first else None
            start = originals[proof][:originals[proof].index('theorem slow_literal_full_flush_loop')].count('\n') + 1
            end = originals[proof][:originals[proof].index('theorem slow_literal_full_flush_loop_content')].count('\n') + 1
            exhausted = any(word in result.stdout.lower() for word in
                            ('maximum recursion depth', 'maximum number of heartbeats',
                             'deterministic timeout', 'interrupted', 'out of memory'))
            if result.returncode == 0 or hit is None or not start <= int(hit.group(1)) < end or exhausted:
                raise RuntimeError(label + ' survived or failed outside actual full literal decision:\n' + result.stdout)
            print('KILLED ' + label + ': ' + first.group(1)
                  + '; synchronized whole slow-body source equality checks; no resource failure', flush=True)


if __name__ == '__main__':
    main()
