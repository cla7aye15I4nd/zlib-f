#!/usr/bin/env python3
"""Require direct proof errors for actual DICT return and continuation bugs."""
from pathlib import Path
import os
import re
import shutil
import subprocess
import tempfile


def main():
    root = Path(__file__).resolve().parents[2]
    source = Path('ZlibF/Zlib/inflate.c.lean')
    proof = Path('ZlibF/Proof/inflate.c.dictionary-dispatch.lean')
    original = (root / source).read_text()
    checked = (root / proof).read_text()
    variants = (
        ('wrong-dictionary-return', 'Ex.ret Z_NEED_DICT', 'Ex.ret Z_OK', 'inflate_DICT_wait_run'),
        ('wrong-input-accounting', 'l.in_ - z.avail_in', 'l.out_ - z.avail_in', 'inflate_DICT_wait_run'),
        ('wrong-checksum-reset', 's with check := v', 's with check := 0', 'inflate_DICT_ready_cut'),
        ('wrong-dictionary-continuation', 'setMode c.st TYPE', 'setMode c.st STORED', 'inflate_DICT_ready_cut'),
    )
    env = os.environ.copy()
    env['LC_ALL'] = 'C'
    target = 'ZlibF.Proof.«inflate.c.dictionary-dispatch»'

    def build(where):
        return subprocess.run(['lake', 'build', target], cwd=where, env=env, text=True,
                              stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=600)

    with tempfile.TemporaryDirectory(prefix='inflate-dictionary-dispatch-') as directory:
        scratch = Path(directory)
        for file in ('lakefile.toml', 'lean-toolchain'):
            shutil.copy2(root / file, scratch / file)
        shutil.copytree(root / 'ZlibF', scratch / 'ZlibF')
        shutil.copytree(root / '.lake', scratch / '.lake', ignore=shutil.ignore_patterns('*.tmp.*'))
        baseline = build(scratch)
        if baseline.returncode:
            raise RuntimeError('baseline failed:\n' + baseline.stdout)
        print('baseline: actual dictionary request and TYPE continuation check', flush=True)
        for label, old, new, theorem in variants:
            a = original.index('def inflate_DICT (')
            b = original.index('def inflate_DICTID (', a)
            section = original[a:b]
            if section.count(old) != 1:
                raise RuntimeError('ambiguous actual DICT mutation: ' + label)
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
        print('PASS: four actual dictionary mutants; no resource failures', flush=True)


if __name__ == '__main__':
    main()
