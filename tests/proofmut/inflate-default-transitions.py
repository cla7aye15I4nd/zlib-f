#!/usr/bin/env python3
"""Check actual reset/prime body mutations with the full default J in scope.

The positive baseline includes the complete public state-preserving result
and both reset and prime transports. Negative builds check the affected
source callee first, so unrelated parallel compilation failures cannot
replace the required direct proof error. No contracts replace any proof.
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
    original = (root / source).read_text()
    cases = (
        ('reset-keep-bad-held', 'inflateResetKeep', 'hold := 0, bits := 0', 'hold := 1, bits := 0',
         'base', 'resetKeep_run'),
        ('reset-keep-bad-sane', 'inflateResetKeep', 'sane := 1', 'sane := 0', 'base', 'resetKeep_run'),
        ('reset-keep-bad-request', 'inflateResetKeep', 'sane := 1', 'sane := 1, reqbits := 0',
         'base', 'resetKeep_run'),
        ('reset-bad-requested-wrapper', 'inflateReset', 'wrap := s.reqwrap', 'wrap := s.reqwrap, reqwrap := 0',
         'reset', 'inflateReset_run'),
        ('reset-bad-window-count', 'inflateReset', 'wsize := 0', 'wsize := 1', 'reset', 'inflateReset_run'),
        ('prime-clear-bad-held', 'inflatePrime', 'hold := 0, bits := 0', 'hold := 1, bits := 0',
         'misc2', 'inflatePrime_spec'),
        ('prime-drop-mask', 'inflatePrime', '(value.toInt64 &&& m).toInt32', 'value',
         'misc2', 'inflatePrime_spec'),
        ('prime-bad-total-limit', 'inflatePrime', 's.bits + i2u bits > 32', 's.bits + i2u bits > 33',
         'misc2', 'inflatePrime_spec'),
        ('prime-subtract-count', 'inflatePrime', 'bits := s.bits + i2u bits', 'bits := s.bits - i2u bits',
         'misc2', 'inflatePrime_spec'),
    )
    env = os.environ.copy()
    env['LC_ALL'] = 'C'

    def build(where, target):
        return subprocess.run(['lake', 'build', 'ZlibF.Proof.«inflate.c.' + target + '»'],
                              cwd=where, env=env, text=True, stdout=subprocess.PIPE,
                              stderr=subprocess.STDOUT, timeout=600)

    with tempfile.TemporaryDirectory(prefix='inflate-default-transitions-') as directory:
        scratch = Path(directory)
        for name in ('lakefile.toml', 'lean-toolchain'):
            shutil.copy2(root / name, scratch / name)
        shutil.copytree(root / 'ZlibF', scratch / 'ZlibF')
        shutil.copytree(root / '.lake', scratch / '.lake', ignore=shutil.ignore_patterns('*.tmp.*', 'Index.*'))
        baseline = build(scratch, 'prime-default-state')
        if baseline.returncode:
            raise RuntimeError('full default-state baseline failed:\n' + baseline.stdout)
        print('baseline: complete public state result and reset/prime J transports check', flush=True)
        for label, function, old, new, module, theorem in cases:
            start = original.index('def ' + function + ' (')
            stop = original.index('\n/--', start)
            lines = original[start:stop].splitlines(keepends=True)
            hits = [i for i, line in enumerate(lines) if not line.lstrip().startswith('--') and old in line]
            if len(hits) != 1 or lines[hits[0]].count(old) != 1:
                raise RuntimeError('ambiguous source edit: ' + label)
            lines[hits[0]] = lines[hits[0]].replace(old, new)
            (scratch / source).write_text(original[:start] + ''.join(lines) + original[stop:])
            result = build(scratch, module)
            proof = Path('ZlibF/Proof/inflate.c.' + module + '.lean')
            text = (root / proof).read_text()
            start = text.index('theorem ' + theorem + ' ')
            end = re.search(r'\n(?:theorem|/--|end)\b', text[start:])
            low = text[:start].count('\n') + 1
            high = len(text.splitlines()) if end is None else low + text[start:start + end.start()].count('\n')
            first = re.search(r'^error: ([^\n]+)', result.stdout, re.M)
            hit = re.match(re.escape(str(proof)) + r':(\d+):', first.group(1)) if first else None
            exhausted = any(term in result.stdout.lower() for term in (
                'maximum recursion depth', 'maximum number of heartbeats', 'deterministic timeout'))
            if result.returncode == 0 or hit is None or not low <= int(hit.group(1)) <= high or exhausted:
                raise RuntimeError(label + ' lacks a direct non-resource proof failure:\n' + result.stdout)
            print('KILLED ' + label + ': ' + first.group(1), flush=True)
        print('PASS: nine actual reset/prime mutants; no resource failures', flush=True)


if __name__ == '__main__':
    main()
