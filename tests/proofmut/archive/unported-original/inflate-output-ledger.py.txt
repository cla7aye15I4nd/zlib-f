#!/usr/bin/env python3
"""Reject real source mutations of inflate output charging and segment-base timing.

The positive baseline includes the actual public-call counter accounting.
Negative builds check only the affected source frame chain first and require
an error in the corresponding function proof, never a resource failure.
"""
from pathlib import Path
import os
import re
import shutil
import subprocess
import tempfile


def main():
    root = Path(__file__).resolve().parents[2]
    paths = (Path('ZlibF/Zlib/inflate.c.lean'), Path('ZlibF/Zlib/inffast.c.lean'))
    originals = {path: (root / path).read_text() for path in paths}
    cases = (
        ('dictionary-output-charge', paths[0], 'inflate_DICT',
         'adler := v', 'adler := v, total_out := z.total_out + 1',
         'output-total-modes', 'output-total-modes', 'outputTotalFrameX_inflate_DICT'),
        ('fast-writeback-output-charge', paths[1], 'inflate_fast',
         'next_in := in_', 'next_in := in_, total_out := sm.total_out + 1',
         'output-total-modes', 'output-total-fast', 'outputTotalFrameM_inflate_fast'),
        ('fast-diagnostic-output-charge', paths[1], 'badData',
         'msg := p', 'msg := p, total_out := st.total_out + 1',
         'output-total-modes', 'output-total-fast', 'outputTotalFrameM_fast_badData'),
        ('literal-corrupts-output-base', paths[0], 'inflate_LIT',
         'put := p, left := l.left - 1', 'put := p, left := l.left - 1, out_ := l.out_ + 1',
         'output-base-modes', 'output-base-modes', 'outputBaseX_inflate_LIT'),
        ('check-missing-output-charge', paths[0], 'inflate_CHECK',
         'total_out := z.total_out + l.out_.toUInt64', 'total_out := z.total_out',
         'main.check', 'main.check', 'inflate_CHECK_run'),
        ('check-wrong-output-rebase', paths[0], 'inflate_CHECK',
         'out_ := l.left }', 'out_ := l.left + 1 }',
         'main.check', 'main.check', 'inflate_CHECK_run'),
    )
    env = os.environ.copy()
    env['LC_ALL'] = 'C'

    def build(where, target):
        return subprocess.run(['lake', 'build', 'ZlibF.Proof.«inflate.c.' + target + '»'],
                              cwd=where, env=env, text=True, stdout=subprocess.PIPE,
                              stderr=subprocess.STDOUT, timeout=600)

    def copy_cache_file(source, destination):
        try:
            return shutil.copy2(source, destination)
        except FileNotFoundError as error:
            # Cache writers may replace an unrelated artifact while copying.
            # Missing required artifacts are rebuilt by the baseline below.
            if str(error.filename) == str(source):
                return str(destination)
            raise

    with tempfile.TemporaryDirectory(prefix='inflate-output-ledger-') as directory:
        scratch = Path(directory)
        for name in ('lakefile.toml', 'lean-toolchain'):
            shutil.copy2(root / name, scratch / name)
        shutil.copytree(root / 'ZlibF', scratch / 'ZlibF')
        shutil.copytree(root / '.lake', scratch / '.lake', copy_function=copy_cache_file,
                        ignore=shutil.ignore_patterns('*.tmp.*', 'Index.*'))
        baseline = build(scratch, 'default-result')
        if baseline.returncode:
            raise RuntimeError('complete public counter-accounting baseline failed:\n' + baseline.stdout)
        print('baseline: actual public result has seven return codes and both ordinary-return counters', flush=True)
        for label, path, function, old, new, target, suffix, theorem in cases:
            for original_path, text in originals.items():
                (scratch / original_path).write_text(text)
            original = originals[path]
            start = original.index('def ' + function + ' (')
            stop = original.find('/--', start)
            if stop < 0:
                stop = original.index('\nend ', start)
            lines = original[start:stop].splitlines(keepends=True)
            hits = [i for i, line in enumerate(lines) if not line.lstrip().startswith('--') and old in line]
            if len(hits) != 1 or lines[hits[0]].count(old) != 1:
                raise RuntimeError('ambiguous source mutation: ' + label)
            lines[hits[0]] = lines[hits[0]].replace(old, new)
            (scratch / path).write_text(original[:start] + ''.join(lines) + original[stop:])
            result = build(scratch, target)
            proof = Path('ZlibF/Proof/inflate.c.' + suffix + '.lean')
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
        print('PASS: six actual output-ledger mutants; no resource failures', flush=True)


if __name__ == '__main__':
    main()
