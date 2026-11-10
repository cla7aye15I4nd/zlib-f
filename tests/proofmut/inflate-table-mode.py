#!/usr/bin/env python3
"""Require direct proof errors for actual TABLE counts and continuation bugs."""
from pathlib import Path
import os
import re
import shutil
import subprocess
import tempfile


def main():
    root = Path(__file__).resolve().parents[2]
    source = Path('ZlibF/Zlib/inflate.c.lean')
    proof = Path('ZlibF/Proof/inflate.c.main.table.lean')
    original = (root / source).read_text()
    checked = (root / proof).read_text()
    variants = (
        ('short-count-read', 'NEEDBITS 14', 'NEEDBITS 13', 'inflate_TABLE_run', 'table'),
        ('relaxed-length-count', 's.nlen > 286 || s.ndist > 30',
         's.nlen > 287 || s.ndist > 30', 'inflate_TABLE_run', 'table'),
        ('wrong-code-count-base', 'ncode := b + 4', 'ncode := b + 5', 'inflate_TABLE_run', 'table'),
        ('wrong-initial-prefix', '«have» := 0, mode := LENLENS',
         '«have» := 1, mode := LENLENS', 'inflate_TABLE_run', 'table'),
    )
    dispatch_variants = (
        ('wrong-TABLE-dispatch', 'then inflate_TABLE c', 'then inflate_COPY c', 'inflate_dispatch_TABLE', 'dispatch'),
        ('wrong-LENLENS-dispatch', 'then inflate_LENLENS c', 'then inflate_TABLE c', 'inflate_dispatch_LENLENS', 'dispatch'),
        ('wrong-CODELENS-dispatch', 'then inflate_CODELENS c', 'then inflate_LEN_ c', 'inflate_dispatch_CODELENS', 'dispatch'),
    )
    variants += dispatch_variants
    env = os.environ.copy()
    env['LC_ALL'] = 'C'
    target = 'ZlibF.Proof.«inflate.c.construction-default-state»'

    def build(where):
        return subprocess.run(['lake', 'build', target], cwd=where, env=env, text=True,
                              stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=600)

    with tempfile.TemporaryDirectory(prefix='inflate-table-mode-') as directory:
        scratch = Path(directory)
        for file in ('lakefile.toml', 'lean-toolchain'):
            shutil.copy2(root / file, scratch / file)
        shutil.copytree(root / 'ZlibF', scratch / 'ZlibF')
        shutil.copytree(root / '.lake', scratch / '.lake', ignore=shutil.ignore_patterns('*.tmp.*', 'Index.*'))
        baseline = build(scratch)
        if baseline.returncode:
            raise RuntimeError('baseline failed:\n' + baseline.stdout)
        print('baseline: complete actual TABLE construction chain and J check', flush=True)
        for label, old, new, theorem, stage in variants:
            if stage == 'table':
                a = original.index('def inflate_TABLE (')
                b = original.index('def inflate_COPY (', a)
                proof = Path('ZlibF/Proof/inflate.c.main.table.lean')
            else:
                a = original.index('def inflate_dispatch (')
                b = original.index('def inflate_run (', a)
                proof = Path('ZlibF/Proof/inflate.c.table-mode.lean')
            checked = (root / proof).read_text()
            section = original[a:b]
            if section.count(old) != 1:
                raise RuntimeError('ambiguous actual TABLE mutation: ' + label)
            (scratch / source).write_text(original[:a] + section.replace(old, new) + original[b:])
            result = build(scratch)
            first = re.search(r'^error: ([^\n]+)', result.stdout, re.MULTILINE)
            hit = re.match(re.escape(str(proof)) + r':(\d+):', first.group(1)) if first else None
            begin = checked.index('theorem ' + theorem + ' ')
            tail = checked[begin:]
            end = re.search(r'\n(?:theorem|/--|end)\b', tail)
            low = checked[:begin].count('\n') + 1
            high = len(checked.splitlines()) if end is None else low + tail[:end.start()].count('\n')
            exhausted = any(word in result.stdout.lower() for word in (
                'maximum recursion depth', 'maximum number of heartbeats', 'deterministic timeout'))
            if result.returncode == 0 or hit is None or not low <= int(hit.group(1)) <= high or exhausted:
                raise RuntimeError(label + ' lacks a direct non-resource proof failure:\n' + result.stdout)
            print('KILLED ' + label + ': ' + first.group(1), flush=True)
        print('PASS: seven actual construction mutants; no resource failures', flush=True)


if __name__ == '__main__':
    main()
