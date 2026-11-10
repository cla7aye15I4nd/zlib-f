#!/usr/bin/env python3
"""Require direct proof failures for forged actual inflate return codes."""
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
    cases = (
        ('dictionary-forged-code', 'inflate_DICT', 'throw (Ex.ret Z_NEED_DICT)', 'throw (Ex.ret 42)',
         'modes', 'exitCodesX_inflate_DICT'),
        ('done-forged-direct-code', 'inflate_DONE', 'throw Ex.leave', 'throw (Ex.ret 42)',
         'modes', 'exitCodesX_inflate_DONE'),
        ('memory-forged-code', 'inflate_dispatch', 'throw (Ex.ret Z_MEM_ERROR)', 'throw (Ex.ret 42)',
         'run', 'exitCodesX_inflate_dispatch'),
        ('stream-forged-code', 'inflate_dispatch', 'throw (Ex.ret Z_STREAM_ERROR)', 'throw (Ex.ret 42)',
         'run', 'exitCodesX_inflate_dispatch'),
    )
    env = os.environ.copy()
    env['LC_ALL'] = 'C'

    def build(where):
        return subprocess.run(['lake', 'build', 'ZlibF.Proof.«inflate.c.exit-code-run»'],
                              cwd=where, env=env, text=True, stdout=subprocess.PIPE,
                              stderr=subprocess.STDOUT, timeout=600)

    with tempfile.TemporaryDirectory(prefix='inflate-exit-codes-') as directory:
        scratch = Path(directory)
        for name in ('lakefile.toml', 'lean-toolchain'):
            shutil.copy2(root / name, scratch / name)
        shutil.copytree(root / 'ZlibF', scratch / 'ZlibF')
        shutil.copytree(root / '.lake', scratch / '.lake', ignore=shutil.ignore_patterns('*.tmp.*', 'Index.*'))
        baseline = build(scratch)
        if baseline.returncode:
            raise RuntimeError('actual complete direct-return baseline failed:\n' + baseline.stdout)
        print('baseline: actual full mode switch and complete inflate_run direct exits classify', flush=True)
        for label, function, old, new, suffix, theorem in cases:
            start = original.index('def ' + function + ' (')
            stop = original.index('/--', start)
            lines = original[start:stop].splitlines(keepends=True)
            hits = [i for i, line in enumerate(lines) if not line.lstrip().startswith('--') and old in line]
            if len(hits) != 1 or lines[hits[0]].count(old) != 1:
                raise RuntimeError('ambiguous source mutation: ' + label)
            lines[hits[0]] = lines[hits[0]].replace(old, new)
            (scratch / source).write_text(original[:start] + ''.join(lines) + original[stop:])
            result = build(scratch)
            proof = Path('ZlibF/Proof/inflate.c.exit-code-' + suffix + '.lean')
            checked = (scratch / proof).read_text()
            first = re.search(r'^error: ([^\n]+)', result.stdout, re.M)
            hit = re.match(re.escape(str(proof)) + r':(\d+):', first.group(1)) if first else None
            start = checked.index('theorem ' + theorem + ' ')
            end = re.search(r'\n(?:theorem|/--|end)\b', checked[start:])
            low = checked[:start].count('\n') + 1
            high = len(checked.splitlines()) if end is None else low + checked[start:start + end.start()].count('\n')
            exhausted = any(term in result.stdout.lower() for term in (
                'maximum recursion depth', 'maximum number of heartbeats', 'deterministic timeout'))
            if result.returncode == 0 or hit is None or exhausted or not low <= int(hit.group(1)) <= high:
                raise RuntimeError(label + ' lacks a direct non-resource function-proof failure:\n' + result.stdout)
            print('KILLED ' + label + ': ' + first.group(1), flush=True)
        print('PASS: four actual direct-return mutants; no resource failures', flush=True)


if __name__ == '__main__':
    main()
