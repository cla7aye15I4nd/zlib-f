#!/usr/bin/env python3
"""Check the actual fast LEN call and its exact LOAD/back continuation."""
from pathlib import Path
import os
import re
import shutil
import subprocess
import tempfile


def main():
    root = Path(__file__).resolve().parents[2]
    source = Path('ZlibF/Zlib/inflate.c.lean')
    proof = Path('ZlibF/Proof/inflate.c.fast-entry.lean')
    original = (root / source).read_text()
    original_proof = (root / proof).read_text()
    variants = (
        ('fast-call-wrong-start', 'inflate_fast c.strm l.out_', 'inflate_fast c.strm l.left',
         'inflate_LEN_fast_raw_cut_progress'),
        ('fast-call-shifted-start', 'inflate_fast c.strm l.out_', 'inflate_fast c.strm (l.out_ + 1)',
         'inflate_LEN_fast_raw_cut_progress'),
        ('fast-call-omitted', 'inflate_fast c.strm l.out_', 'pure ()', 'inflate_LEN_fast_raw_cut_progress'),
        ('fast-type-wrong-back', 'back := -1', 'back := 0', 'inflateAfterFast_run'),
    )
    env = os.environ.copy()
    env['LC_ALL'] = 'C'
    target = 'ZlibF.Proof.«inflate.c.construction-default»'

    def run(where):
        return subprocess.run(['lake', 'build', target], cwd=where, env=env, text=True,
                              stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=600)

    with tempfile.TemporaryDirectory(prefix='inflate-fast-entry-') as directory:
        scratch = Path(directory)
        for name in ('lakefile.toml', 'lean-toolchain'):
            shutil.copy2(root / name, scratch / name)
        shutil.copytree(root / 'ZlibF', scratch / 'ZlibF')
        shutil.copytree(root / '.lake', scratch / '.lake', ignore=shutil.ignore_patterns('*.tmp.*', 'Index.*'))
        baseline = run(scratch)
        if baseline.returncode:
            raise RuntimeError('unmutated baseline failed:\n' + baseline.stdout)
        print('baseline: actual fast LEN prefix, callee and suffix check', flush=True)
        for label, old, new, theorem in variants:
            a = original.index('def inflate_LEN (')
            b = original.index('/-- `case LEN_:', a)
            part = original[a:b]
            if theorem == 'inflateAfterFast_run':
                # Only the fast TYPE post-call write, before the slow branch.
                stop = part.index('  -- state->back = 0;')
                first = part[:stop]
                if first.count(old) != 1:
                    raise RuntimeError('ambiguous fast back write')
                changed = first.replace(old, new) + part[stop:]
                pa = original_proof.index('def inflateAfterFast (')
                pb = original_proof.index('/-- The actual fast branch', pa)
                literal = original_proof[pa:pb]
                if literal.count(old) != 1:
                    raise RuntimeError('ambiguous source continuation')
                (scratch / proof).write_text(original_proof[:pa] + literal.replace(old, new) + original_proof[pb:])
            else:
                if part.count(old) != 1:
                    raise RuntimeError('ambiguous actual fast call')
                changed = part.replace(old, new)
                (scratch / proof).write_text(original_proof)
            (scratch / source).write_text(original[:a] + changed + original[b:])
            result = run(scratch)
            first = re.search(r'^error: ([^\n]+)', result.stdout, re.MULTILINE)
            hit = re.match(re.escape(str(proof)) + r':(\d+):', first.group(1)) if first else None
            text = (scratch / proof).read_text()
            a = text.index('theorem ' + theorem + ' ')
            tail = text[a:]
            end = re.search(r'\n(?:theorem|/--|end)\b', tail)
            low = text[:a].count('\n') + 1
            high = len(text.splitlines()) if end is None else low + tail[:end.start()].count('\n')
            exhausted = any(term in result.stdout.lower() for term in (
                'maximum recursion depth', 'maximum number of heartbeats', 'deterministic timeout'))
            if result.returncode == 0 or hit is None or not low <= int(hit.group(1)) <= high or exhausted:
                raise RuntimeError(label + ' lacks a direct non-resource proof failure:\n' + result.stdout)
            print('KILLED ' + label + ': ' + first.group(1), flush=True)
        print('PASS: four actual fast-entry mutants; no resource failures', flush=True)


if __name__ == '__main__':
    main()
