#!/usr/bin/env python3
"""Reject actual window-return faults in the composed inf_leave proof.

Literal source cuts are synchronized; the operational postconditions stay
fixed. The isolated baseline omits only the earlier overlapping raw-call
proof, with no replacement assumptions.
"""
from pathlib import Path
import os
import re
import shutil
import subprocess
import sys
import tempfile


def replace_part(text, begin, end, old, new):
    a = text.index(begin)
    b = text.index(end, a)
    part = text[a:b]
    lines = part.splitlines(keepends=True)
    hits = [i for i, line in enumerate(lines) if not line.lstrip().startswith('--') and old in line]
    if len(hits) != 1 or lines[hits[0]].count(old) != 1:
        raise RuntimeError('ambiguous window mutation: ' + begin)
    indent = lines[hits[0]][:len(lines[hits[0]]) - len(lines[hits[0]].lstrip())]
    lines[hits[0]] = lines[hits[0]].replace(old, new.replace('\n', '\n' + indent))
    return text[:a] + ''.join(lines) + text[b:]


def main():
    root = Path(__file__).resolve().parents[2]
    paths = (Path('ZlibF/Zlib/inflate.c.lean'),
             Path('ZlibF/Proof/inflate.c.leave-restore.lean'),
             Path('ZlibF/Proof/inflate.c.leave-window.lean'))
    originals = [(root / path).read_text() for path in paths]
    variants = (
        ('window-failure-wrong-mode', 'setMode c.st MEM', 'setMode c.st BAD'),
        ('window-failure-wrong-result', 'return Z_MEM_ERROR', 'return Z_DATA_ERROR'),
        ('window-wrong-copy-count', 'updatewindow c.strm z.next_out (l.out_ - z.avail_out)',
         'updatewindow c.strm z.next_out (l.out_ - z.avail_out + 1)'),
        ('window-failure-charges-input', 'setMode c.st MEM',
         'wrZ c.strm (fun z => { z with total_in := z.total_in + 1 })\nsetMode c.st MEM'),
        ('window-failure-charges-output', 'setMode c.st MEM',
         'wrZ c.strm (fun z => { z with total_out := z.total_out + 1 })\nsetMode c.st MEM'),
    )
    env = os.environ.copy()
    env['LC_ALL'] = 'C'
    memory_result = '--memory-result' in sys.argv[1:]
    target = ('ZlibF.Proof.«inflate.c.default-memory»' if memory_result else
              'ZlibF.Proof.«inflate.c.leave-window»')

    def run(directory, selected=None):
        return subprocess.run(['lake', 'build', selected or target], cwd=directory, env=env, text=True,
                              stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=600)

    def copy_cache_file(source, destination):
        try:
            return shutil.copy2(source, destination)
        except FileNotFoundError as error:
            if str(error.filename) == str(source):
                return str(destination)
            raise

    with tempfile.TemporaryDirectory(prefix='inflate-leave-window-') as directory:
        scratch = Path(directory)
        for name in ('lakefile.toml', 'lean-toolchain'):
            shutil.copy2(root / name, scratch / name)
        shutil.copytree(root / 'ZlibF', scratch / 'ZlibF')
        shutil.copytree(root / '.lake', scratch / '.lake', copy_function=copy_cache_file,
                        ignore=shutil.ignore_patterns('*.tmp.*', 'Index.*'))
        stored = scratch / 'ZlibF/Proof/inflate.c.stored-call.lean'
        text = stored.read_text()
        a = text.rindex('/--', 0, text.index('theorem inflate_leave_raw_finish_done'))
        b = text.rindex('/--', 0, text.index('theorem LOAD_run'))
        c = text.rindex('/--', 0, text.index('theorem inflate_run_raw_copy'))
        stored.write_text(text[:a] + text[b:c] + '\nend Zlib.Inflate.Proofs\n')
        baseline = run(scratch)
        if baseline.returncode:
            raise RuntimeError('isolated baseline failed:\n' + baseline.stdout)
        print('baseline: ' + ('complete public memory timing and output-byte result checks' if memory_result else
                              'complete actual zlib-wrapper inf_leave boundary checks'), flush=True)
        for label, old, new in variants:
            source = replace_part(originals[0], 'def inflate_leave (', '/-- `int ZEXPORT inflate(', old, new)
            restore = replace_part(originals[1], 'def leaveAfterRestore (', '/-- Stream fields', old, new)
            window = replace_part(originals[2], 'def leaveWithWindow (', '/-- Expose the actual callee', old, new)
            for path, text in zip(paths, (source, restore, window)):
                (scratch / path).write_text(text)
            result = run(scratch, 'ZlibF.Proof.«inflate.c.leave-window»')
            first = re.search(r'^error: ([^\n]+)', result.stdout, re.MULTILINE)
            hit = re.match(re.escape(str(paths[2])) + r':(\d+):', first.group(1)) if first else None
            a = window.index('theorem leaveWithWindow_safe ')
            b = window.index('/-- The complete actual inf_leave', a)
            low, high = window[:a].count('\n') + 1, window[:b].count('\n') + 1
            exhausted = any(term in result.stdout.lower() for term in (
                'maximum recursion depth', 'maximum number of heartbeats', 'deterministic timeout'))
            if result.returncode == 0 or hit is None or not low <= int(hit.group(1)) < high or exhausted:
                raise RuntimeError(label + ' lacks a direct non-resource proof failure:\n' + result.stdout)
            print('KILLED ' + label + ': ' + first.group(1), flush=True)
        print('PASS: five actual window-return/counter mutants; no resource failures', flush=True)


if __name__ == '__main__':
    main()
