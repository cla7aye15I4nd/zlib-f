#!/usr/bin/env python3
"""Reject fixed-stream-field corruption in each actual mode and main body.

Copy each translated function without changing its callees, and replay its
source frame proof. A namespace-local copied function isolates that proof
from older safety proofs which also depend on the original translation.
The baseline copies must check before any mutation is tested.
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
    metadata = '--memory-meta' in sys.argv[1:]
    stem = 'memory-meta-frame' if metadata else 'stream-frame'
    frame_prefix = 'memoryMetaFrameX_' if metadata else 'streamFrameX_'
    modes = (root / f'ZlibF/Proof/inflate.c.{stem}-modes.lean').read_text()
    main_proofs = (root / f'ZlibF/Proof/inflate.c.{stem}-run.lean').read_text()
    names = re.findall(r'^theorem ' + frame_prefix + r'inflate_(\w+) ', modes, re.M) + ['run']
    functions = []
    proofs = []
    for name in names:
        original = 'inflate_' + name
        copied = 'copied_' + original
        start = source.index('def ' + original + ' (')
        stop = source.index('\n/--', start)
        function = source[start:stop].replace('def ' + original + ' ', 'def ' + copied + ' ', 1)
        text = main_proofs if name == 'run' else modes
        start = text.index('theorem ' + frame_prefix + original + ' ')
        stop = text.find('\n/--', start)
        if stop < 0:
            stop = text.index('\nend Zlib.Inflate.Proofs', start)
        proof = text[start:stop].replace('theorem ' + frame_prefix + original + ' ',
                                        'theorem copied_frame_' + name + ' ', 1)
        proof = proof.replace('(' + original + ' context)', '(' + copied + ' context)')
        proof = proof.replace('unfold ' + original + '\n', 'unfold ' + copied + '\n')
        functions.append(function)
        proofs.append(proof)
    header = f'''import ZlibF.Proof.«inflate.c.{stem}-run»
namespace Zlib.Inflate.Proofs.StreamFrameMutants
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public Zlib.Inflate.Proofs
open Zlib.Crc32 (crc32)
open Zlib.Inffast (inflate_fast)
open Zlib.Inftrees (inflate_table inflate_fixed)
open Zlib.Adler32 (adler32)
set_option autoImplicit false
'''
    env = os.environ.copy()
    env['LC_ALL'] = 'C'
    with tempfile.TemporaryDirectory(prefix='inflate-stream-frame-') as directory:
        path = Path(directory) / 'frame-mutants.lean'

        def check(mutant=None):
            chunks = [header]
            ranges = {}
            for name, function, proof in zip(names, functions, proofs):
                if name == mutant:
                    arg = '_c' if name == 'DONE' else 'c'
                    mutation = ('  let _ ← allocLocalB 1\n' if metadata else
                                f'  wrZ {arg}.strm fun z => {{ z with reserved := z.reserved + 1 }}\n')
                    function = function.replace(': X Unit := do\n', ': X Unit := do\n' + mutation, 1)
                chunks.append(function + '\n')
                low = ''.join(chunks).count('\n') + 1
                chunks.append(proof + '\n')
                ranges[name] = (low, ''.join(chunks).count('\n'))
            chunks.append('end Zlib.Inflate.Proofs.StreamFrameMutants\n')
            path.write_text(''.join(chunks))
            result = subprocess.run(['lake', 'env', 'lean', str(path)], cwd=root, env=env,
                                    text=True, stdout=subprocess.PIPE,
                                    stderr=subprocess.STDOUT, timeout=120)
            return result, ranges

        baseline, _ = check()
        if baseline.returncode:
            raise RuntimeError('baseline failed:\n' + baseline.stdout)
        print(f'baseline: {len(names)} exact source copies and their frame proofs check', flush=True)
        for name in names:
            result, ranges = check(name)
            errors = re.findall(r'^.*frame-mutants\.lean:(\d+):\d+: error: ([^\n]+)', result.stdout, re.M)
            low, high = ranges[name]
            exhausted = any(term in result.stdout.lower() for term in (
                'maximum recursion depth', 'maximum number of heartbeats', 'deterministic timeout'))
            if result.returncode == 0 or not errors or exhausted or any(
                    not low <= int(line) <= high for line, _ in errors):
                raise RuntimeError(name + ' lacks a direct non-resource proof failure:\n' + result.stdout)
            print('KILLED ' + name + ': ' + errors[0][1], flush=True)
        print(f'PASS: {len(names)} ' + ('allocation-metadata' if metadata else 'fixed-field') +
              ' mutants; no resource failures', flush=True)


if __name__ == '__main__':
    main()
