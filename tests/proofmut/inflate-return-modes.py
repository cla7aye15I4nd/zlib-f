#!/usr/bin/env python3
"""Reject real source mutations of the actual default return-mode links.

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
        ('done-wrong-mode', paths[0], 'inflate_DONE',
         'modify fun l => { l with ret := Z_STREAM_END }',
         'setMode _c.st BAD\n  modify fun l => { l with ret := Z_STREAM_END }',
         'main.simple', (('main.simple', 'inflate_DONE_run'),)),
        ('length-wrong-done-mode', paths[0], 'inflate_LENGTH',
         'setMode c.st DONE', 'setMode c.st BAD',
         'main.check', (('main.check', 'inflate_LENGTH_skip'),)),
        ('dictionary-wrong-wait-mode', paths[0], 'inflate_DICT',
         'throw (Ex.ret Z_NEED_DICT)', 'wrS c.st (fun s => { s with mode := TYPE })\n    throw (Ex.ret Z_NEED_DICT)',
         'dictionary-dispatch', (('dictionary-dispatch', 'inflate_DICT_wait_run'),)),
        ('bad-wrong-terminal-mode', paths[0], 'inflate_dispatch',
         'modify fun l => { l with ret := Z_DATA_ERROR }',
         'setMode c.st LEN\n    modify fun l => { l with ret := Z_DATA_ERROR }',
         'terminal-dispatch', (('terminal-dispatch', 'inflate_dispatch_terminal_run'),)),
        ('memory-wrong-terminal-mode', paths[0], 'inflate_dispatch',
         'else if m == MEM then throw (Ex.ret Z_MEM_ERROR)',
         'else if m == MEM then\n    setMode c.st BAD\n    throw (Ex.ret Z_MEM_ERROR)',
         'terminal-dispatch', (('terminal-dispatch', 'inflate_dispatch_terminal_run'),)),
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
        baseline = build(scratch, 'default-mode-result')
        if baseline.returncode:
            raise RuntimeError('complete return-register mode baseline failed:\n' + baseline.stdout)
        print('baseline: actual public entry/body/free, progress and all four return-mode links', flush=True)
        for label, path, function, old, new, target, expected in cases:
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
            first = re.search(r'^error: ([^\n]+)', result.stdout, re.M)
            accepted = False
            for suffix, theorem in expected:
                proof = Path('ZlibF/Proof/inflate.c.' + suffix + '.lean')
                checked = (scratch / proof).read_text()
                hit = re.match(re.escape(str(proof)) + r':(\d+):', first.group(1)) if first else None
                declaration = re.search(r'^theorem\s+' + re.escape(theorem) + r'\b', checked, re.M)
                if declaration is None:
                    raise RuntimeError('missing expected function proof: ' + theorem)
                start = declaration.start()
                end = re.search(r'\n(?:theorem|/--|end)\b', checked[start:])
                low = checked[:start].count('\n') + 1
                high = len(checked.splitlines()) if end is None else low + checked[start:start + end.start()].count('\n')
                # Lean can locate a declaration's failed definitional equation
                # at its attached attribute or docstring command span.
                source_lines = checked.splitlines()
                while low > 1 and source_lines[low - 2].strip().startswith('@[') and source_lines[low - 2].strip().endswith(']'):
                    low -= 1
                if low > 1 and source_lines[low - 2].strip().endswith('-/'):
                    doc_start = low - 2
                    while doc_start >= 0 and '/--' not in source_lines[doc_start]:
                        doc_start -= 1
                    if doc_start >= 0:
                        low = doc_start + 1
                accepted = accepted or (hit is not None and low <= int(hit.group(1)) <= high)
            exhausted = any(term in result.stdout.lower() for term in (
                'maximum recursion depth', 'maximum number of heartbeats', 'deterministic timeout'))
            if result.returncode == 0 or not accepted or exhausted:
                raise RuntimeError(label + ' lacks a direct non-resource function-proof failure:\n' + result.stdout)
            print('KILLED ' + label + ': ' + first.group(1), flush=True)
        print('PASS: five actual return-mode mutants; no resource failures', flush=True)


if __name__ == '__main__':
    main()
