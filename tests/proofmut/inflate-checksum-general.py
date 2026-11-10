#!/usr/bin/env python3
"""Reject actual CRC-branch faults in the generic inflate return proof."""
from pathlib import Path
import os
import re
import shutil
import subprocess
import tempfile


def main():
    root = Path(__file__).resolve().parents[2]
    source = Path('ZlibF/Zlib/inflate.c.lean')
    proof = Path('ZlibF/Proof/inflate.c.checksum-general.lean')
    original = (root / source).read_text()
    variants = (
        ('checksum-crc-wrong-seed', 'then crc32 check buf len', 'then crc32 (check + 1) buf len'),
        ('checksum-crc-wrong-length', 'then crc32 check buf len', 'then crc32 check buf (len + 1)'),
    )
    env = os.environ.copy()
    env['LC_ALL'] = 'C'
    target = 'ZlibF.Proof.«inflate.c.leave-all-wrappers»'

    def run(where):
        return subprocess.run(['lake', 'build', target], cwd=where, env=env, text=True,
                              stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=600)

    with tempfile.TemporaryDirectory(prefix='inflate-checksum-general-') as directory:
        scratch = Path(directory)
        for name in ('lakefile.toml', 'lean-toolchain'):
            shutil.copy2(root / name, scratch / name)
        shutil.copytree(root / 'ZlibF', scratch / 'ZlibF')
        shutil.copytree(root / '.lake', scratch / '.lake', ignore=shutil.ignore_patterns('*.tmp.*'))
        baseline = run(scratch)
        if baseline.returncode:
            raise RuntimeError('unmutated baseline failed:\n' + baseline.stdout)
        print('baseline: complete all-wrapper inf_leave boundary checks', flush=True)
        for label, old, new in variants:
            a = original.index('def UPDATE_CHECK (')
            b = original.index('/-- `CRC2(', a)
            part = original[a:b]
            if part.count(old) != 1:
                raise RuntimeError('ambiguous actual CRC-branch mutation')
            (scratch / source).write_text(original[:a] + part.replace(old, new) + original[b:])
            result = run(scratch)
            first = re.search(r'^error: ([^\n]+)', result.stdout, re.MULTILINE)
            hit = re.match(re.escape(str(proof)) + r':(\d+):', first.group(1)) if first else None
            text = (scratch / proof).read_text()
            low = text[:text.index('theorem UPDATE_CHECK_all_views ')].count('\n') + 1
            high = len(text.splitlines())
            exhausted = any(term in result.stdout.lower() for term in (
                'maximum recursion depth', 'maximum number of heartbeats', 'deterministic timeout'))
            if result.returncode == 0 or hit is None or not low <= int(hit.group(1)) <= high or exhausted:
                raise RuntimeError(label + ' lacks a direct non-resource proof failure:\n' + result.stdout)
            print('KILLED ' + label + ': ' + first.group(1), flush=True)
        print('PASS: two actual CRC-branch mutants; no resource failures', flush=True)


if __name__ == '__main__':
    main()
