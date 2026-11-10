#!/usr/bin/env python3
"""Require direct proof failures for corrupted actual inflate input bases."""
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
        ('done-corrupt-base', 'inflate_DONE', 'ret := Z_STREAM_END', 'ret := Z_STREAM_END, in_ := l.in_ + 1',
         'modes', 'inputBaseX_inflate_DONE'),
        ('check-corrupt-base', 'inflate_CHECK', 'out_ := l.left', 'out_ := l.left, in_ := l.in_ + 1',
         'modes', 'inputBaseX_inflate_CHECK'),
        ('literal-corrupt-base', 'inflate_LIT', 'put := p, left := l.left - 1', 'put := p, left := l.left - 1, in_ := l.in_ + 1',
         'modes', 'inputBaseX_inflate_LIT'),
        ('dictionary-corrupt-base', 'inflate_DICT', 'if (← rdS c.st (·.havedict)) == 0 then',
         'modify fun l => { l with in_ := l.in_ + 1 }\n  if (← rdS c.st (·.havedict)) == 0 then',
         'modes', 'inputBaseX_inflate_DICT'),
        ('error-corrupt-base', 'inflate_dispatch', 'ret := Z_DATA_ERROR', 'ret := Z_DATA_ERROR, in_ := l.in_ + 1',
         'loop', 'inputBaseX_inflate_dispatch'),
    )
    env = os.environ.copy()
    env['LC_ALL'] = 'C'

    def build(where, selected='entry'):
        return subprocess.run(['lake', 'build', 'ZlibF.Proof.«inflate.c.input-base-' + selected + '»'],
                              cwd=where, env=env, text=True, stdout=subprocess.PIPE,
                              stderr=subprocess.STDOUT, timeout=600)

    with tempfile.TemporaryDirectory(prefix='inflate-input-base-') as directory:
        scratch = Path(directory)
        for name in ('lakefile.toml', 'lean-toolchain'):
            shutil.copy2(root / name, scratch / name)
        shutil.copytree(root / 'ZlibF', scratch / 'ZlibF')
        shutil.copytree(root / '.lake', scratch / '.lake', ignore=shutil.ignore_patterns('*.tmp.*', 'Index.*'))
        baseline = build(scratch)
        if baseline.returncode:
            raise RuntimeError('actual complete input-base entry/loop baseline failed:\n' + baseline.stdout)
        print('baseline: actual default entry sets the input base; all modes and full loop retain it', flush=True)
        for label, function, old, new, suffix, theorem in cases:
            start = original.index('def ' + function + ' (')
            stop = original.index('/--', start)
            lines = original[start:stop].splitlines(keepends=True)
            hits = [i for i, line in enumerate(lines) if not line.lstrip().startswith('--') and old in line]
            if len(hits) != 1 or lines[hits[0]].count(old) != 1:
                raise RuntimeError('ambiguous source mutation: ' + label)
            lines[hits[0]] = lines[hits[0]].replace(old, new)
            (scratch / source).write_text(original[:start] + ''.join(lines) + original[stop:])
            result = build(scratch, 'loop')
            proof = Path('ZlibF/Proof/inflate.c.input-base-' + suffix + '.lean')
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
        print('PASS: five actual input-base mutants; no resource failures', flush=True)


if __name__ == '__main__':
    main()
