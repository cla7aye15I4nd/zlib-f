#!/usr/bin/env python3
"""Check the actual default HEAD mode against direct source mutations.

The literal header-check suffix is synchronized for mutations within that
suffix. Its fixed test predicates and exact expected state writes remain
unchanged, so the source equation remains checked before execution fails.
"""
from pathlib import Path
import os
import re
import shutil
import subprocess
import tempfile


def main():
    root = Path(__file__).resolve().parents[2]
    source = Path('ZlibF/Zlib/inflate.c.lean')
    proof = Path('ZlibF/Proof/inflate.c.header-default.lean')
    original = (root / source).read_text()
    original_proof = (root / proof).read_text()
    guard = 'if (s.wrap &&& 1) == 0 || ((b8 <<< 8).toUInt64 + (l.hold >>> 8)) % 31 != 0 then'
    window = 'if len > 15 || (s.wbits != 0 && len > s.wbits) then'
    variants = (
        ('header-dispatch-wrong-mode', 'then inflate_HEAD c', 'then inflate_FLAGS c', 'dispatch', 'inflate_dispatch_HEAD'),
        ('header-short-pull', 'NEEDBITS 16', 'NEEDBITS 8', 'prefix', 'inflate_HEAD_zlib_window_prefix_count'),
        ('header-dropped-check', guard, 'if false then', 'suffix', 'headDefaultCheck_bad_header'),
        ('header-dropped-window-check', window, 'if false then', 'suffix', 'headDefaultCheck_bad_window'),
        ('header-wrong-distance-limit', 'shl32 1 len', 'shl32 2 len', 'suffix', 'headDefaultCheck_accept'),
        ('header-wrong-wrapper-flag', 'dmax := dm, flags := 0', 'dmax := dm, flags := 1', 'suffix', 'headDefaultCheck_accept'),
    )
    env = os.environ.copy()
    env['LC_ALL'] = 'C'
    target = 'ZlibF.Proof.«inflate.c.header-default»'

    def run(where):
        return subprocess.run(['lake', 'build', target], cwd=where, env=env, text=True,
                              stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=600)

    with tempfile.TemporaryDirectory(prefix='inflate-default-header-') as directory:
        scratch = Path(directory)
        for name in ('lakefile.toml', 'lean-toolchain'):
            shutil.copy2(root / name, scratch / name)
        shutil.copytree(root / 'ZlibF', scratch / 'ZlibF')
        shutil.copytree(root / '.lake', scratch / '.lake', ignore=shutil.ignore_patterns('*.tmp.*'))
        baseline = run(scratch)
        if baseline.returncode:
            raise RuntimeError('unmutated baseline failed:\n' + baseline.stdout)
        print('baseline: actual default HEAD and complete boundary packet check', flush=True)
        for label, old, new, stage, theorem in variants:
            if stage == 'dispatch':
                a = original.index('def inflate_dispatch (')
                b = original.index('def inflate_run (', a)
            else:
                a = original.index('def inflate_HEAD (')
                b = original.index('/-- The `switch', a)
            part = original[a:b]
            lines = part.splitlines(keepends=True)
            hits = [i for i, line in enumerate(lines) if not line.lstrip().startswith('--') and old in line]
            if len(hits) != 1 or lines[hits[0]].count(old) != 1:
                raise RuntimeError('ambiguous actual header mutation: ' + label)
            lines[hits[0]] = lines[hits[0]].replace(old, new)
            (scratch / source).write_text(original[:a] + ''.join(lines) + original[b:])
            if stage == 'suffix':
                a = original_proof.index('def headDefaultCheck (')
                b = original_proof.index('/-- The real default HEAD prefix', a)
                part = original_proof[a:b]
                lines = part.splitlines(keepends=True)
                hits = [i for i, line in enumerate(lines) if not line.lstrip().startswith('--') and old in line]
                if len(hits) != 1:
                    raise RuntimeError('ambiguous literal header suffix')
                lines[hits[0]] = lines[hits[0]].replace(old, new)
                text = original_proof[:a] + ''.join(lines) + original_proof[b:]
            else:
                text = original_proof
            (scratch / proof).write_text(text)
            result = run(scratch)
            first = re.search(r'^error: ([^\n]+)', result.stdout, re.MULTILINE)
            hit = re.match(re.escape(str(proof)) + r':(\d+):', first.group(1)) if first else None
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
        print('PASS: six actual default-header mutants; no resource failures', flush=True)


if __name__ == '__main__':
    main()
