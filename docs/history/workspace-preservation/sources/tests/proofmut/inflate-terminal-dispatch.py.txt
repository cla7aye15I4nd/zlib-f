#!/usr/bin/env python3
"""Reject wrong actual terminal/error returns in their execution proofs."""
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
    terminal = Path('ZlibF/Proof/inflate.c.terminal-dispatch.lean')
    simple = Path('ZlibF/Proof/inflate.c.main.simple.lean')
    variants = (
        ('wrong-stream-end', 'done', 'ret := Z_STREAM_END', 'ret := Z_OK', simple, 'inflate_DONE_run'),
        ('wrong-data-error', 'dispatch', 'ret := Z_DATA_ERROR', 'ret := Z_OK', terminal, 'inflate_dispatch_terminal_run'),
        ('wrong-memory-error', 'dispatch', 'Ex.ret Z_MEM_ERROR', 'Ex.ret Z_OK', terminal, 'inflate_dispatch_terminal_run'),
        ('wrong-sync-error', 'dispatch', 'Ex.ret Z_STREAM_ERROR', 'Ex.ret Z_OK', terminal, 'inflate_dispatch_terminal_run'),
    )
    env = os.environ.copy()
    env['LC_ALL'] = 'C'

    def build(where):
        return subprocess.run(['lake', 'build', 'ZlibF.Proof.«inflate.c.terminal-dispatch»'], cwd=where,
                              env=env, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=600)

    with tempfile.TemporaryDirectory(prefix='inflate-terminal-dispatch-') as directory:
        scratch = Path(directory)
        for file in ('lakefile.toml', 'lean-toolchain'):
            shutil.copy2(root / file, scratch / file)
        shutil.copytree(root / 'ZlibF', scratch / 'ZlibF')
        shutil.copytree(root / '.lake', scratch / '.lake', ignore=shutil.ignore_patterns('*.tmp.*'))
        baseline = build(scratch)
        if baseline.returncode:
            raise RuntimeError('baseline failed:\n' + baseline.stdout)
        print('baseline: actual terminal/error dispatch checks', flush=True)
        for label, stage, old, new, proof, theorem in variants:
            if stage == 'done':
                a = original.index('def inflate_DONE (')
                b = original.index('def inflate_LENGTH (', a)
            else:
                a = original.index('def inflate_dispatch (')
                b = original.index('def inflate_run (', a)
            section = original[a:b]
            if section.count(old) != 1:
                raise RuntimeError('ambiguous terminal mutation: ' + label)
            (scratch / source).write_text(original[:a] + section.replace(old, new) + original[b:])
            result = build(scratch)
            first = re.search(r'^error: ([^\n]+)', result.stdout, re.MULTILINE)
            hit = re.match(re.escape(str(proof)) + r':(\d+):', first.group(1)) if first else None
            text = (root / proof).read_text()
            begin = text.index('theorem ' + theorem + ' ')
            tail = text[begin:]
            end = re.search(r'\n(?:theorem|/--|end)\b', tail)
            declaration_start = text.rindex('/--', 0, begin)
            low = text[:declaration_start].count('\n') + 1
            high = len(text.splitlines()) if end is None else low + tail[:end.start()].count('\n')
            exhausted = any(word in result.stdout.lower() for word in (
                'maximum recursion depth', 'maximum number of heartbeats', 'deterministic timeout'))
            if result.returncode == 0 or hit is None or not low <= int(hit.group(1)) <= high or exhausted:
                raise RuntimeError(label + ' lacks a direct non-resource proof failure:\n' + result.stdout)
            print('KILLED ' + label + ': ' + first.group(1), flush=True)
        print('PASS: four actual terminal/error mutants; no resource failures', flush=True)


if __name__ == '__main__':
    main()
