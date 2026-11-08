#!/usr/bin/env python3
"""Reject decoding-helper regressions at the independent content bridge.

These mutate heap-free decoding and trace definitions, not the C source.
Actual C consumption mutants are checked separately by deflate-slow-match.
"""
from pathlib import Path
import os
import re
import shutil
import subprocess
import tempfile


def main():
    root = Path(__file__).resolve().parents[2]
    lake = shutil.which('lake') or str(Path.home() / '.elan/bin/lake')
    source = Path('ZlibF/Math/DeflateSymbolTrace.lean')
    original = (root / source).read_text()
    cases = (
        ('decoder-literal-value', 'history ++ [UInt8.ofNat s.value]',
         'history ++ [UInt8.ofNat (s.value + 1)]', 'meaning_expands'),
        ('decoder-match-distance', 'else ZlibF.Spec.copyBack [] s.distance (s.value + 3) history',
         'else ZlibF.Spec.copyBack [] (s.distance + 1) (s.value + 3) history', 'meaning_expands'),
        ('decoder-match-length', 'else ZlibF.Spec.copyBack [] s.distance (s.value + 3) history',
         'else ZlibF.Spec.copyBack [] s.distance (s.value + 2) history', 'meaning_expands'),
        ('trace-byte-position', 's.Meaning input (base + represented xs) → Trace input base (xs ++ [s])',
         's.Meaning input (base + represented xs + 1) → Trace input base (xs ++ [s])', 'Trace.expands'),
    )
    with tempfile.TemporaryDirectory(prefix='deflate-symbol-decoding-') as directory:
        scratch = Path(directory)
        for name in ('lakefile.toml', 'lean-toolchain'):
            shutil.copy2(root / name, scratch / name)
        shutil.copytree(root / 'ZlibF', scratch / 'ZlibF')
        shutil.copytree(root / '.lake/build', scratch / '.lake/build')

        def build(module):
            return subprocess.run([lake, 'build', module], cwd=scratch,
                                  env=dict(os.environ, LC_ALL='C'), text=True,
                                  stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=240)

        baseline = build('ZlibF.Proof.«deflate.c.engine.content-refill»')
        if baseline.returncode:
            raise RuntimeError('positive actual content-preserving execution:\n' + baseline.stdout)
        print('baseline: actual initialized/refilled slow boundary retains independent decoded content', flush=True)
        for label, old, new, theorem in cases:
            if original.count(old) != 1:
                raise RuntimeError('ambiguous decoding-helper mutation: ' + label)
            (scratch / source).write_text(original.replace(old, new))
            result = build('ZlibF.Math.DeflateSymbolTrace')
            start = original[:original.index('theorem ' + theorem)].count('\n') + 1
            following = original.find('\ntheorem ', original.index('theorem ' + theorem) + len(theorem))
            end = len(original.splitlines()) + 1 if following < 0 else original[:following].count('\n') + 1
            errors = re.findall(r'^error: (' + re.escape(str(source)) + r':(\d+):[^\n]*)',
                                result.stdout, re.MULTILINE)
            hit = next((line for line, number in errors if start <= int(number) < end), None)
            resource = any(term in result.stdout.lower() for term in (
                'maximum recursion depth', 'maximum number of heartbeats', 'deep recursion detected',
                'deterministic timeout', 'interrupted', 'out of memory'))
            if result.returncode == 0 or hit is None or resource:
                raise RuntimeError(label + ' survived or failed inconclusively:\n' + result.stdout)
            print('KILLED ' + label + ': ' + hit, flush=True)


if __name__ == '__main__':
    main()
