#!/usr/bin/env python3
"""Reject changes to incorrect CRC table pointers."""
from pathlib import Path
import os
import re
import shutil
import subprocess
import tempfile

MAIN = Path(__file__).resolve().parents[2]
CASES = (
    ('wrong-offset', 'pure (Ptr.ref URef.st_crc_table 0)', 'pure (Ptr.ref URef.st_crc_table 1)'),
    ('wrong-table', 'pure (Ptr.ref URef.st_crc_table 0)', 'pure (Ptr.ref URef.st_x2n_table 0)'),
    ('null-pointer', 'pure (Ptr.ref URef.st_crc_table 0)', 'pure .null'),
)

def main():
    env = os.environ.copy()
    env['LC_ALL'] = 'C'
    with tempfile.TemporaryDirectory(prefix='get-crc-table-mutants-') as tmp:
        scratch = Path(tmp)
        for file in ('lakefile.toml', 'lean-toolchain'):
            shutil.copy2(MAIN / file, scratch / file)
        shutil.copytree(MAIN / 'ZlibF', scratch / 'ZlibF')
        shutil.copytree(MAIN / '.lake', scratch / '.lake', ignore=shutil.ignore_patterns('*.tmp.*'))
        def build():
            return subprocess.run(['lake', 'build', 'ZlibF.Proof.«public-get-crc-table»'],
                                  cwd=scratch, env=env, text=True, stdout=subprocess.PIPE,
                                  stderr=subprocess.STDOUT, timeout=600)
        baseline = build()
        if baseline.returncode:
            raise RuntimeError('Unmutated packet failed:\n' + baseline.stdout)
        print('BASELINE PASS', flush=True)
        target = scratch / 'ZlibF/Zlib/crc32.c.lean'
        original = target.read_text()
        prefix, rest = original.split('def get_crc_table :', 1)
        body, suffix = rest.split('/-! ### `crc32_z` -/', 1)
        for name, old, new in CASES:
            if body.count(old) != 1:
                raise RuntimeError('Expected one mutation site: ' + name)
            target.write_text(prefix + 'def get_crc_table :' + body.replace(old, new, 1) +
                              '/-! ### `crc32_z` -/' + suffix)
            result = build()
            errors = re.findall(r'^error: ([^\n]+)', result.stdout, re.MULTILINE)
            if result.returncode == 0 or not any(e.startswith('ZlibF/Proof/public-get-crc-table.lean:') for e in errors):
                raise RuntimeError(name + ' survived or failed outside the function proof:\n' + result.stdout)
            print('KILLED ' + name, flush=True)
            target.write_text(original)

if __name__ == '__main__':
    main()
