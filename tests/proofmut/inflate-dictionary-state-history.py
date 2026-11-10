#!/usr/bin/env python3
"""Reject actual dictionary API mutations with full default-J baseline.

Negative builds check the affected source function proof first. A resource
failure or an error outside an inflateSetDictionary proof is never a kill.
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
    proof = Path('ZlibF/Proof/inflate.c.dict.lean')
    original = (root / source).read_text()
    checked = (root / proof).read_text()
    cases = (
        ('missing-dictionary-flag', 'havedict := 1', 'havedict := 0'),
        ('corrupt-requested-bits', 'havedict := 1', 'havedict := 1, reqbits := 0'),
        ('corrupt-requested-wrapper', 'havedict := 1', 'havedict := 1, reqwrap := 0'),
        ('enable-gzip', 'havedict := 1', 'havedict := 1, wrap := 6'),
        ('wrong-memory-mode', 'setMode st MEM', 'setMode st BAD'),
        ('accept-wrong-checksum', 'if dictid != s.check then return Z_DATA_ERROR',
         'if dictid != s.check then return Z_OK'),
    )
    env = os.environ.copy()
    env['LC_ALL'] = 'C'

    def build_module(where, module):
        return subprocess.run(['lake', 'build', module],
                              cwd=where, env=env, text=True, stdout=subprocess.PIPE,
                              stderr=subprocess.STDOUT, timeout=600)

    def build(where, target, serial=False):
        module = 'ZlibF.Proof.«inflate.c.' + target + '»'
        if serial:
            order = []
            seen = set()

            def visit(name):
                if name in seen or not name.startswith('ZlibF.'):
                    return
                seen.add(name)
                parts = re.findall(r'«[^»]+»|[^.]+', name)
                # A quoted C-file module already has a suffix in its stem.
                path = where.joinpath(*(part.strip('«»') for part in parts[:-1]), parts[-1].strip('«»') + '.lean')
                text = path.read_text()
                for dependency in re.findall(r'^import\s+(\S+)', text, re.M):
                    visit(dependency)
                order.append(name)

            visit(module)
            for dependency in order[:-1]:
                result = build_module(where, dependency)
                if result.returncode:
                    return result
        return build_module(where, module)

    with tempfile.TemporaryDirectory(prefix='inflate-dictionary-state-history-') as directory:
        scratch = Path(directory)
        for name in ('lakefile.toml', 'lean-toolchain'):
            shutil.copy2(root / name, scratch / name)
        shutil.copytree(root / 'ZlibF', scratch / 'ZlibF')
        shutil.copytree(root / '.lake', scratch / '.lake', ignore=shutil.ignore_patterns('*.tmp.*', 'Index.*'))
        baseline = build(scratch, 'dictionary-state-history')
        if baseline.returncode:
            raise RuntimeError('complete default dictionary-J baseline failed:\n' + baseline.stdout)
        print('baseline: full J survives all actual dictionary API outcomes', flush=True)
        for label, old, new in cases:
            start = original.index('def inflateSetDictionary (')
            stop = original.index('/-- `int ZEXPORT inflateGetHeader(', start)
            lines = original[start:stop].splitlines(keepends=True)
            hits = [i for i, line in enumerate(lines) if not line.lstrip().startswith('--') and old in line]
            if len(hits) != 1 or lines[hits[0]].count(old) != 1:
                raise RuntimeError('ambiguous source mutation: ' + label)
            lines[hits[0]] = lines[hits[0]].replace(old, new)
            (scratch / source).write_text(original[:start] + ''.join(lines) + original[stop:])
            result = build(scratch, 'dict', serial=True)
            first = re.search(r'^error: ([^\n]+)', result.stdout, re.M)
            hit = re.match(re.escape(str(proof)) + r':(\d+):', first.group(1)) if first else None
            ranges = []
            for theorem in ('inflateSetDictionary_safe', 'inflateSetDictionary_streamerr', 'inflateSetDictionary_dataerr'):
                start = checked.index('theorem ' + theorem + ' ')
                end = re.search(r'\n(?:theorem|/--|end)\b', checked[start:])
                low = checked[:start].count('\n') + 1
                high = len(checked.splitlines()) if end is None else low + checked[start:start + end.start()].count('\n')
                ranges.append((low, high))
            exhausted = any(term in result.stdout.lower() for term in (
                'maximum recursion depth', 'maximum number of heartbeats', 'deterministic timeout'))
            if result.returncode == 0 or hit is None or exhausted or not any(
                    low <= int(hit.group(1)) <= high for low, high in ranges):
                raise RuntimeError(label + ' lacks a direct non-resource function-proof failure:\n' + result.stdout)
            print('KILLED ' + label + ': ' + first.group(1), flush=True)
        print('PASS: six actual dictionary API mutants; no resource failures', flush=True)


if __name__ == '__main__':
    main()
