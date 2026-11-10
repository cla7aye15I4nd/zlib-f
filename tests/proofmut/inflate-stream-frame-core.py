#!/usr/bin/env python3
"""Replay source frame proofs against copied helper-body corruptions.

Exact copies isolate each proof from older helper clients. The real source
and protected contracts remain unchanged. Every unmodified copy checks first.
"""
from pathlib import Path
import os
import re
import subprocess
import tempfile


def main():
    root = Path(__file__).resolve().parents[2]
    source = (root / 'ZlibF/Zlib/inflate.c.lean').read_text()
    base = (root / 'ZlibF/Proof/inflate.c.stream-frame.lean').read_text()
    primitives = (root / 'ZlibF/Proof/inflate.c.stream-frame-primitives.lean').read_text()
    cases = (
        ('setMsg', primitives, 'streamFrameM_setMsg',
         'stZStream strm { z with msg := p }',
         'stZStream strm { z with msg := p, reserved := z.reserved + 1 }'),
        ('wrZ', base, 'streamFrameM_wrZ', 'stZStream strm (f z)',
         'stZStream strm { f z with reserved := (f z).reserved + 1 }'),
        ('setMode', primitives, 'streamFrameM_setMode',
         'wrS st fun s => { s with mode := m }',
         'do\n  let s ← ldInflateState st\n  wrZ s.strm fun z => { z with reserved := z.reserved + 1 }\n  wrS st fun s => { s with mode := m }'),
    )
    header = '''import ZlibF.Proof.«inflate.c.stream-frame-primitives»
namespace Zlib.Inflate.Proofs.CoreFrameMutants
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs
set_option autoImplicit false
'''
    env = os.environ.copy()
    env['LC_ALL'] = 'C'
    with tempfile.TemporaryDirectory(prefix='inflate-core-frame-') as directory:
        path = Path(directory) / 'core-mutant.lean'
        for name, proof_source, theorem, old, new in cases:
            start = source.index('def ' + name + ' ')
            stop = source.index('\n', start)
            while stop < len(source) and source[stop + 1:stop + 3] == '  ':
                stop = source.index('\n', stop + 1)
            function = source[start:stop].replace('def ' + name + ' ', 'def copied_' + name + ' ', 1)
            start = proof_source.index('theorem ' + theorem + ' ')
            stop = proof_source.find('\ntheorem ', start + 1)
            doc = proof_source.find('\n/--', start + 1)
            end = proof_source.find('\nend ', start + 1)
            stop = min(i for i in [stop, doc, end] if i >= 0)
            proof = proof_source[start:stop].replace('theorem ' + theorem + ' ', 'theorem copied_frame ', 1)
            proof = proof.replace('(' + name + ' ', '(copied_' + name + ' ')
            proof = proof.replace('unfold ' + name + '\n', 'unfold copied_' + name + '\n')
            if name == 'wrZ':
                proof = proof.replace('  intro h value after run\n',
                    '  intro h value after run\n'
                    '  change wrZ (some r) update h = .ok (value, after) at run\n')

            def check(body):
                prefix = header + body + '\n'
                path.write_text(prefix + proof + '\nend Zlib.Inflate.Proofs.CoreFrameMutants\n')
                result = subprocess.run(['lake', 'env', 'lean', str(path)], cwd=root, env=env,
                                        text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=120)
                return result, prefix.count('\n') + 1, (prefix + proof).count('\n') + 1

            baseline, _, _ = check(function)
            if baseline.returncode:
                raise RuntimeError(name + ' baseline failed:\n' + baseline.stdout)
            if function.count(old) != 1:
                raise RuntimeError('ambiguous source edit: ' + name)
            result, low, high = check(function.replace(old, new))
            errors = re.findall(r'^.*core-mutant\.lean:(\d+):\d+: error: ([^\n]+)', result.stdout, re.M)
            exhausted = any(term in result.stdout.lower() for term in (
                'maximum recursion depth', 'maximum number of heartbeats', 'deterministic timeout'))
            if result.returncode == 0 or not errors or exhausted or any(
                    not low <= int(line) <= high for line, _ in errors):
                raise RuntimeError(name + ' lacks a direct non-resource proof failure:\n' + result.stdout)
            print('KILLED ' + name + ': ' + errors[0][1], flush=True)
        print('PASS: three actual helper-body mutants; baselines check; no resource failures', flush=True)


if __name__ == '__main__':
    main()
