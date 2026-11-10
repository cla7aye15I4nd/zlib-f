#!/usr/bin/env python3
"""Reject actual window-allocation and initialization body mutations.

The positive baseline checks the complete returning platform transport.
Negative builds check the affected updatewindow source proofs first, and
accept only direct function-proof failures, never resource failures.
"""
from pathlib import Path
import os
import re
import shutil
import subprocess
import tempfile


def main():
    root = Path(__file__).resolve().parents[2]
    source = Path('ZlibF/Zlib/inflate.c.lean')
    original = (root / source).read_text()
    proof = Path('ZlibF/Proof/inflate.c.uw.lean')
    checked = (root / proof).read_text()
    cases = (
        ('wrong-allocation-size', 'ZALLOCB strm (← shl32 1 s.wbits) 1',
         'ZALLOCB strm (← shl32 1 s.wbits) 2', ('uw_alloc_fail', 'uw_alloc_ok')),
        ('false-allocation-success', 'if w == .null then return 1',
         'if w == .null then return 0', ('uw_alloc_fail',)),
        ('oversized-window-count', 'wsize := ws, wnext := 0, whave := 0',
         'wsize := ws + 1, wnext := 0, whave := 0', ('uw_init',)),
    )
    env = os.environ.copy()
    env['LC_ALL'] = 'C'

    def build(where, target):
        return subprocess.run(['lake', 'build', 'ZlibF.Proof.«inflate.c.' + target + '»'],
                              cwd=where, env=env, text=True, stdout=subprocess.PIPE,
                              stderr=subprocess.STDOUT, timeout=600)

    with tempfile.TemporaryDirectory(prefix='inflate-window-platform-') as directory:
        scratch = Path(directory)
        for name in ('lakefile.toml', 'lean-toolchain'):
            shutil.copy2(root / name, scratch / name)
        shutil.copytree(root / 'ZlibF', scratch / 'ZlibF')
        shutil.copytree(root / '.lake', scratch / '.lake', ignore=shutil.ignore_patterns('*.tmp.*', 'Index.*'))
        baseline = build(scratch, 'window-platform')
        if baseline.returncode:
            raise RuntimeError('returning platform baseline failed:\n' + baseline.stdout)
        print('baseline: existing, new and failed window allocation platform transports check', flush=True)
        for label, old, new, theorems in cases:
            start = original.index('def updatewindow (')
            stop = original.index('\n/-!', start)
            lines = original[start:stop].splitlines(keepends=True)
            hits = [i for i, line in enumerate(lines) if not line.lstrip().startswith('--') and old in line]
            if len(hits) != 1 or lines[hits[0]].count(old) != 1:
                raise RuntimeError('ambiguous source mutation: ' + label)
            lines[hits[0]] = lines[hits[0]].replace(old, new)
            (scratch / source).write_text(original[:start] + ''.join(lines) + original[stop:])
            result = build(scratch, 'uw')
            first = re.search(r'^error: ([^\n]+)', result.stdout, re.M)
            hit = re.match(re.escape(str(proof)) + r':(\d+):', first.group(1)) if first else None
            ranges = []
            for theorem in theorems:
                start = checked.index('theorem ' + theorem + ' ')
                end = re.search(r'\n(?:theorem|/--|end)\b', checked[start:])
                low = checked[:start].count('\n') + 1
                high = len(checked.splitlines()) if end is None else low + checked[start:start + end.start()].count('\n')
                ranges.append((low, high))
            exhausted = any(term in result.stdout.lower() for term in (
                'maximum recursion depth', 'maximum number of heartbeats', 'deterministic timeout'))
            if result.returncode == 0 or hit is None or exhausted or not any(
                    low <= int(hit.group(1)) <= high for low, high in ranges):
                raise RuntimeError(label + ' lacks a direct non-resource proof failure:\n' + result.stdout)
            print('KILLED ' + label + ': ' + first.group(1), flush=True)
        print('PASS: three actual updatewindow mutants; no resource failures', flush=True)


if __name__ == '__main__':
    main()
