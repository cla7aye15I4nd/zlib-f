#!/usr/bin/env python3
"""Build isolated source mutants and require failures in the new gzeof proof."""
from pathlib import Path
import os
import re
import shutil
import subprocess
import tempfile

MAIN = Path(__file__).resolve().parents[2]
CASES = (
    ('null-result', 'if file.isNone then return 0', 'if file.isNone then return 1'),
    ('reader-result', 'return if s.mode == GZ_READ then s.past else 0', 'return 0'),
    ('writer-result', 'return if s.mode == GZ_READ then s.past else 0',
     'return if s.mode == GZ_READ then s.past else 1'),
)

def main():
    env = os.environ.copy()
    env['LC_ALL'] = 'C'
    with tempfile.TemporaryDirectory(prefix='gzeof-mutants-') as tmp:
        scratch = Path(tmp)
        for file in ('lakefile.toml', 'lean-toolchain'):
            shutil.copy2(MAIN / file, scratch / file)
        shutil.copytree(MAIN / 'ZlibF', scratch / 'ZlibF')
        shutil.copytree(MAIN / '.lake', scratch / '.lake',
                        ignore=shutil.ignore_patterns('*.tmp.*'))
        def build():
            return subprocess.run(['lake', 'build', 'ZlibF.Proof.«public-gzeof»'],
                                  cwd=scratch, env=env, text=True,
                                  stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                  timeout=600)
        baseline = build()
        if baseline.returncode:
            raise RuntimeError('Unmutated packet failed:\n' + baseline.stdout)
        print('BASELINE PASS', flush=True)
        target = scratch / 'ZlibF/Zlib/gzlib.c.lean'
        original = target.read_text()
        prefix, rest = original.split('def gzeof (', 1)
        body, suffix = rest.split('/-- `const char * ZEXPORT gzerror', 1)
        for name, old, new in CASES:
            if body.count(old) != 1:
                raise RuntimeError('Expected one mutation site: ' + name)
            target.write_text(prefix + 'def gzeof (' + body.replace(old, new, 1) +
                              '/-- `const char * ZEXPORT gzerror' + suffix)
            result = build()
            errors = re.findall(r'^error: ([^\n]+)', result.stdout, re.MULTILINE)
            expected = [e for e in errors if e.startswith('ZlibF/Proof/public-gzeof.lean:')]
            if result.returncode == 0 or not expected:
                raise RuntimeError(name + ' survived or failed outside the new function proof:\n' + result.stdout)
            print('KILLED ' + name + ': ' + expected[0], flush=True)
            target.write_text(original)

if __name__ == '__main__':
    main()
