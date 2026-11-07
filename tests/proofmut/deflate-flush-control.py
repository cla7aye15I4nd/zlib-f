#!/usr/bin/env python3
"""The actual nonfinal flush wrapper must return need_more on full output."""
from pathlib import Path
import os
import re
import shutil
import subprocess
import tempfile


def main():
    root = Path(__file__).resolve().parents[2]
    source = Path('ZlibF/Zlib/deflate_base.c.lean')
    proof = Path('ZlibF/Proof/deflate.c.engine.flush-control.lean')
    original = (root / source).read_text()
    text = (root / proof).read_text()
    old = 'if last == 0 then return some need_more'
    variants = (
        ('dropped-need-more-return', 'if last == 0 then return none'),
        ('wrong-nonfinal-return', 'if last == 0 then return some finish_started'),
    )
    env = os.environ.copy()
    env['LC_ALL'] = 'C'

    def build(where, target):
        return subprocess.run(['lake', 'build', target], cwd=where, env=env, text=True,
                              stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=600)

    def success(result, label):
        if result.returncode:
            raise RuntimeError(label + ':\n' + result.stdout)

    with tempfile.TemporaryDirectory(prefix='deflate-flush-control-') as name:
        scratch = Path(name)
        for filename in ('lakefile.toml', 'lean-toolchain'):
            shutil.copy2(root / filename, scratch / filename)
        shutil.copytree(root / 'ZlibF', scratch / 'ZlibF')
        shutil.copytree(root / '.lake', scratch / '.lake')
        target = 'ZlibF.Proof.«deflate.c.engine.flush-control»'
        success(build(scratch, target), 'positive real nonfinal control and restored boundary')
        print('baseline: actual nonfinal wrapper preserves content boundary and obeys output-full return', flush=True)
        for label, new in variants:
            left, body = original.split('def FLUSH_BLOCK (', 1)
            if body.count(old) != 1:
                raise RuntimeError('ambiguous nonfinal flush return')
            (scratch / source).write_text(left + 'def FLUSH_BLOCK (' + body.replace(old, new))
            success(build(scratch, 'ZlibF.Zlib.«deflate_base.c»'), label + ' translated macro compiles')
            result = build(scratch, target)
            first = re.search(r'^error: ([^\n]+)', result.stdout, re.MULTILINE)
            hit = re.match(re.escape(str(proof)) + r':(\d+):', first.group(1)) if first else None
            start = text[:text.index('theorem flush_nonfinal_content_boundary')].count('\n') + 1
            exhausted = any(word in result.stdout.lower() for word in
                            ('maximum recursion depth', 'maximum number of heartbeats',
                             'deterministic timeout', 'interrupted', 'out of memory'))
            if result.returncode == 0 or hit is None or int(hit.group(1)) < start or exhausted:
                raise RuntimeError(label + ' survived or failed outside actual nonfinal control:\n' + result.stdout)
            print('KILLED ' + label + ': ' + first.group(1)
                  + '; real translated macro compiles; no resource failure', flush=True)


if __name__ == '__main__':
    main()
