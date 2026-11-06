#!/usr/bin/env python3
"""Reject changes to incorrect results from zlibVersion."""
from pathlib import Path
import os
import re
import shutil
import subprocess
import tempfile

MAIN = Path(__file__).resolve().parents[2]
CASES = (
    ('wrong-string', 'strLit ZLIB_VERSION', 'strLit ""'),
    ('null-pointer', 'strLit ZLIB_VERSION', 'return .null'),
)

def main():
    env = os.environ.copy()
    env['LC_ALL'] = 'C'
    with tempfile.TemporaryDirectory(prefix='zlib-version-mutants-') as tmp:
        scratch = Path(tmp)
        for file in ('lakefile.toml', 'lean-toolchain'):
            shutil.copy2(MAIN / file, scratch / file)
        shutil.copytree(MAIN / 'ZlibF', scratch / 'ZlibF')
        shutil.copytree(MAIN / '.lake', scratch / '.lake', ignore=shutil.ignore_patterns('*.tmp.*'))
        def build():
            return subprocess.run(['lake', 'build', 'ZlibF.Proof.«public-zlib-version»'],
                                  cwd=scratch, env=env, text=True, stdout=subprocess.PIPE,
                                  stderr=subprocess.STDOUT, timeout=600)
        baseline = build()
        if baseline.returncode:
            raise RuntimeError('Unmutated packet failed:\n' + baseline.stdout)
        print('BASELINE PASS', flush=True)
        target = scratch / 'ZlibF/Zlib/zutil.c.lean'
        original = target.read_text()
        prefix, rest = original.split('def zlibVersion :', 1)
        body, suffix = rest.split('/-- `uLong ZEXPORT zlibCompileFlags', 1)
        for name, old, new in CASES:
            if body.count(old) != 1:
                raise RuntimeError('Expected one mutation site: ' + name)
            target.write_text(prefix + 'def zlibVersion :' + body.replace(old, new, 1) +
                              '/-- `uLong ZEXPORT zlibCompileFlags' + suffix)
            result = build()
            errors = re.findall(r'^error: ([^\n]+)', result.stdout, re.MULTILINE)
            if result.returncode == 0 or not any(e.startswith('ZlibF/Proof/public-zlib-version.lean:') for e in errors):
                raise RuntimeError(name + ' survived or failed outside the function proof:\n' + result.stdout)
            print('KILLED ' + name, flush=True)
            target.write_text(original)

if __name__ == '__main__':
    main()
