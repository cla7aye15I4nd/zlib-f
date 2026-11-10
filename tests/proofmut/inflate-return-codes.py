#!/usr/bin/env python3
"""Reject real source mutations of CHECK/LENGTH/DONE return-code rules.

Every exact source baseline is checked first. Each wrong register write must
fail inside its corresponding actual mode proof without resource errors.
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
        ('done-wrong-return-register', paths[0], 'inflate_DONE',
         'ret := Z_STREAM_END', 'ret := 7',
         'return-codes', 'returnAllowedX_inflate_DONE'),
        ('length-wrong-leave-register', paths[0], 'inflate_LENGTH',
         'inflate_DONE c', 'modify fun l => { l with ret := 7 }\n  throw Ex.leave',
         'return-codes', 'returnAllowedX_inflate_LENGTH'),
        ('check-corrupts-return-register', paths[0], 'inflate_CHECK',
         'out_ := l.out_ - l.left', 'out_ := l.out_ - l.left, ret := 7',
         'return-codes', 'returnAllowedX_inflate_CHECK'),
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

    with tempfile.TemporaryDirectory(prefix='inflate-return-register-') as directory:
        scratch = Path(directory)
        for name in ('lakefile.toml', 'lean-toolchain'):
            shutil.copy2(root / name, scratch / name)
        shutil.copytree(root / 'ZlibF', scratch / 'ZlibF')
        shutil.copytree(root / '.lake', scratch / '.lake', copy_function=copy_cache_file,
                        ignore=shutil.ignore_patterns('*.tmp.*', 'Index.*'))
        baseline = build(scratch, 'default-result')
        if baseline.returncode:
            raise RuntimeError('complete return-register mode baseline failed:\n' + baseline.stdout)
        print('baseline: actual public result plus CHECK/LENGTH/DONE return-code rules', flush=True)
        for label, path, function, old, new, suffix, theorem in cases:
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
            result = build(scratch, 'return-codes')
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
        print('PASS: three actual trailer-return mutants; no resource failures', flush=True)


if __name__ == '__main__':
    main()
