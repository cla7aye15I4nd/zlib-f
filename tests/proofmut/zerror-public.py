#!/usr/bin/env python3
"""Reject incorrect error-code handling in zError."""
from pathlib import Path
import os
import re
import shutil
import subprocess
import tempfile

MAIN = Path(__file__).resolve().parents[2]
CASES = (
    ('lower-bound', 'err < -6 || err > 2', 'err < -5 || err > 2'),
    ('upper-bound', 'err < -6 || err > 2', 'err < -6 || err > 1'),
    ('message-index', 'then 9 else 2 - err', 'then 9 else 1 - err'),
    ('out-of-range-index', 'then 9 else 2 - err', 'then 0 else 2 - err'),
)

def main():
    env = os.environ.copy()
    env['LC_ALL'] = 'C'
    with tempfile.TemporaryDirectory(prefix='zerror-mutants-') as tmp:
        scratch = Path(tmp)
        for file in ('lakefile.toml', 'lean-toolchain'):
            shutil.copy2(MAIN / file, scratch / file)
        shutil.copytree(MAIN / 'ZlibF', scratch / 'ZlibF')
        shutil.copytree(MAIN / '.lake', scratch / '.lake', ignore=shutil.ignore_patterns('*.tmp.*'))
        def build():
            return subprocess.run(['lake', 'build', 'ZlibF.Proof.«public-zerror»'],
                                  cwd=scratch, env=env, text=True, stdout=subprocess.PIPE,
                                  stderr=subprocess.STDOUT, timeout=600)
        baseline = build()
        if baseline.returncode:
            raise RuntimeError('Unmutated packet failed:\n' + baseline.stdout)
        print('BASELINE PASS', flush=True)
        target = scratch / 'ZlibF/Zlib/zutil.c.lean'
        original = target.read_text()
        prefix, rest = original.split('def zError (', 1)
        body, suffix = rest.split('/-- `voidpf ZLIB_INTERNAL zcalloc', 1)
        for name, old, new in CASES:
            if body.count(old) != 1:
                raise RuntimeError('Expected one mutation site: ' + name)
            target.write_text(prefix + 'def zError (' + body.replace(old, new, 1) +
                              '/-- `voidpf ZLIB_INTERNAL zcalloc' + suffix)
            result = build()
            errors = re.findall(r'^error: ([^\n]+)', result.stdout, re.MULTILINE)
            if result.returncode == 0 or not any(e.startswith('ZlibF/Proof/public-zerror.lean:') for e in errors):
                raise RuntimeError(name + ' survived or failed outside the function proof:\n' + result.stdout)
            print('KILLED ' + name, flush=True)
            target.write_text(original)

if __name__ == '__main__':
    main()
