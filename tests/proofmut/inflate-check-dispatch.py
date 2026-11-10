#!/usr/bin/env python3
"""Require direct proof errors for actual CHECK accounting and trailer bugs."""
from pathlib import Path
import os
import re
import shutil
import subprocess
import tempfile


def main():
    root = Path(__file__).resolve().parents[2]
    source = Path('ZlibF/Zlib/inflate.c.lean')
    proof = Path('ZlibF/Proof/inflate.c.check-dispatch.lean')
    original = (root / source).read_text()
    checked = (root / proof).read_text()
    variants = (
        ('short-trailer-read', 'NEEDBITS 32', 'NEEDBITS 16', 'inflate_CHECK_views_run'),
        ('wrong-output-total', 'total_out := z.total_out + l.out_.toUInt64',
         'total_out := z.total_out + l.left.toUInt64', 'inflate_CHECK_views_run'),
        ('wrong-state-total', 'total := s.total + l.out_.toUInt64',
         'total := s.total + l.left.toUInt64', 'inflate_CHECK_views_run'),
        ('lost-accounting-base', 'out_ := l.left', 'out_ := l.out_', 'inflate_CHECK_views_run'),
        ('wrong-trailer-endianness', 'then l.hold else ZSWAP32 l.hold',
         'then l.hold else l.hold', 'inflate_CHECK_views_run'),
    )
    env = os.environ.copy()
    env['LC_ALL'] = 'C'
    target = 'ZlibF.Proof.«inflate.c.check-dispatch»'

    def build(where):
        return subprocess.run(['lake', 'build', target], cwd=where, env=env, text=True,
                              stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=600)

    with tempfile.TemporaryDirectory(prefix='inflate-check-dispatch-') as directory:
        scratch = Path(directory)
        for file in ('lakefile.toml', 'lean-toolchain'):
            shutil.copy2(root / file, scratch / file)
        shutil.copytree(root / 'ZlibF', scratch / 'ZlibF')
        shutil.copytree(root / '.lake', scratch / '.lake', ignore=shutil.ignore_patterns('*.tmp.*'))
        # Omit the older raw-block-only theorem in this scratch build.
        # The complete actual-view theorem below is independently checked.
        legacy = scratch / 'ZlibF/Proof/inflate.c.main.check.lean'
        text = legacy.read_text()
        a = text.index('/-- `case CHECK:` with `wrap ≠ 0`.')
        legacy.write_text(text[:a] + '\nend Zlib.Inflate.Proofs\n')
        baseline = build(scratch)
        if baseline.returncode:
            raise RuntimeError('baseline failed:\n' + baseline.stdout)
        print('baseline: complete actual CHECK mode and default rank check', flush=True)
        for label, old, new, theorem in variants:
            a = original.index('def inflate_CHECK (')
            b = original.index('def inflate_LIT (', a)
            lines = original[a:b].splitlines(keepends=True)
            hits = [i for i, line in enumerate(lines) if not line.lstrip().startswith('--') and old in line]
            if len(hits) != 1:
                raise RuntimeError('ambiguous actual CHECK mutation: ' + label)
            lines[hits[0]] = lines[hits[0]].replace(old, new)
            (scratch / source).write_text(original[:a] + ''.join(lines) + original[b:])
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
        print('PASS: five actual CHECK mutants; no resource failures', flush=True)


if __name__ == '__main__':
    main()
