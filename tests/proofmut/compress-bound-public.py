#!/usr/bin/env python3
"""Reject changes to incorrect compression bound calculations."""
from pathlib import Path
import os
import re
import shutil
import subprocess
import tempfile

MAIN = Path(__file__).resolve().parents[2]
CASES = (
    ('first-shift', 'sourceLen >>> 12', 'sourceLen >>> 11'),
    ('second-shift', 'sourceLen >>> 14', 'sourceLen >>> 13'),
    ('third-shift', 'sourceLen >>> 25', 'sourceLen >>> 24'),
    ('constant', ' + 13\n', ' + 12\n'),
    ('overflow-guard', 'if bound < sourceLen then', 'if bound > sourceLen then'),
    ('wrapper-result', '  compressBound_z sourceLen\n', '  compressBound_z sourceLen + 1\n'),
)

def main():
    env = os.environ.copy()
    env['LC_ALL'] = 'C'
    with tempfile.TemporaryDirectory(prefix='compress-bound-mutants-') as tmp:
        scratch = Path(tmp)
        for file in ('lakefile.toml', 'lean-toolchain'):
            shutil.copy2(MAIN / file, scratch / file)
        shutil.copytree(MAIN / 'ZlibF', scratch / 'ZlibF')
        shutil.copytree(MAIN / '.lake', scratch / '.lake', ignore=shutil.ignore_patterns('*.tmp.*'))
        def build():
            return subprocess.run(['lake', 'build', 'ZlibF.Proof.«public-compress-bound»'],
                                  cwd=scratch, env=env, text=True, stdout=subprocess.PIPE,
                                  stderr=subprocess.STDOUT, timeout=600)
        baseline = build()
        if baseline.returncode:
            raise RuntimeError('Unmutated packet failed:\n' + baseline.stdout)
        print('BASELINE PASS', flush=True)
        target = scratch / 'ZlibF/Zlib/compress.c.lean'
        original = target.read_text()
        prefix, rest = original.split('def compressBound_z (', 1)
        body, suffix = rest.split('end Zlib.Compress', 1)
        for name, old, new in CASES:
            if body.count(old) != 1:
                raise RuntimeError('Expected one mutation site: ' + name)
            target.write_text(prefix + 'def compressBound_z (' + body.replace(old, new, 1) +
                              'end Zlib.Compress' + suffix)
            result = build()
            errors = re.findall(r'^error: ([^\n]+)', result.stdout, re.MULTILINE)
            if result.returncode == 0 or not any(e.startswith('ZlibF/Proof/public-compress-bound.lean:') for e in errors):
                raise RuntimeError(name + ' survived or failed outside the function proof:\n' + result.stdout)
            print('KILLED ' + name, flush=True)
            target.write_text(original)

if __name__ == '__main__':
    main()
