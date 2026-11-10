#!/usr/bin/env python3
"""Reject public-entry faults and local-buffer leaks with its actual proof.

A namespace-local exact copy of the translated entry isolates this proof
from earlier restricted examples. Its actual run and leave callees are
unchanged. The unmodified copy must check before source mutations run.
"""
from pathlib import Path
import os
import sys
import re
import subprocess
import tempfile


def main():
    root = Path(__file__).resolve().parents[2]
    source = (root / 'ZlibF/Zlib/inflate.c.lean').read_text()
    state_mode = '--state' in sys.argv[1:]
    module = 'default-public-state' if state_mode else 'default-public'
    theorem = 'inflate_default_raw_state_safe' if state_mode else 'inflate_default_raw_safe'
    proofs = (root / f'ZlibF/Proof/inflate.c.{module}.lean').read_text()
    start = source.index('def inflate (')
    stop = source.index('\n/--', start)
    original = source[start:stop].replace('def inflate (', 'def copied_inflate (', 1)
    start = proofs.index('theorem ' + theorem + ' ')
    stop = proofs.find('\n/--', start)
    if stop < 0:
        stop = proofs.index('\nend Zlib.Inflate.Proofs', start)
    proof = proofs[start:stop].replace('theorem ' + theorem + ' ', 'theorem copied_safe ', 1)
    proof = proof.replace('(inflate (some r)', '(copied_inflate (some r)')
    proof = proof.replace('unfold C.run inflate\n', 'unfold C.run copied_inflate\n')
    variants = (
        ('omitted-local-free', '  freeB hbuf\n', '  pure ()\n'),
        ('wrong-local-free', '  freeB hbuf\n', '  freeB .null\n'),
        ('double-local-free', '  freeB hbuf\n', '  freeB hbuf\n  freeB hbuf\n'),
        ('null-state-cast', 'castInflateState z.state', 'castInflateState none'),
        ('faulting-main-body', 'inflate_run c', '(monadLift (ub "mutant") : X Unit)'),
    )
    header = f'''import ZlibF.Proof.«inflate.c.{module}»
namespace Zlib.Inflate.Proofs.DefaultPublicMutants
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public Zlib.Inflate.Proofs
set_option autoImplicit false
'''
    env = os.environ.copy()
    env['LC_ALL'] = 'C'
    with tempfile.TemporaryDirectory(prefix='inflate-default-public-') as directory:
        path = Path(directory) / 'public-mutant.lean'

        def check(function):
            prefix = header + function + '\n'
            path.write_text(prefix + proof + '\nend Zlib.Inflate.Proofs.DefaultPublicMutants\n')
            result = subprocess.run(['lake', 'env', 'lean', str(path)], cwd=root, env=env,
                                    text=True, stdout=subprocess.PIPE,
                                    stderr=subprocess.STDOUT, timeout=120)
            return result, prefix.count('\n') + 1, (prefix + proof).count('\n') + 1

        baseline, _, _ = check(original)
        if baseline.returncode:
            raise RuntimeError('baseline failed:\n' + baseline.stdout)
        print('baseline: exact public entry and its ' + ('full default-state proof' if state_mode else
              'complete safety proof') + ' check', flush=True)
        for label, old, new in variants:
            if original.count(old) != 1:
                raise RuntimeError('ambiguous source edit: ' + label)
            result, low, high = check(original.replace(old, new))
            errors = re.findall(r'^.*public-mutant\.lean:(\d+):\d+: error: ([^\n]+)', result.stdout, re.M)
            exhausted = any(term in result.stdout.lower() for term in (
                'maximum recursion depth', 'maximum number of heartbeats', 'deterministic timeout'))
            if result.returncode == 0 or not errors or exhausted or any(
                    not low <= int(line) <= high for line, _ in errors):
                raise RuntimeError(label + ' lacks a direct non-resource proof failure:\n' + result.stdout)
            print('KILLED ' + label + ': ' + errors[0][1], flush=True)
        print('PASS: five public-entry mutants; no resource failures', flush=True)


if __name__ == '__main__':
    main()
