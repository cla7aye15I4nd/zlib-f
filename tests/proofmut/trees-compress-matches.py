#!/usr/bin/env python3
"""Reject actual compress_block match regressions in execution proofs.

The complete source equality and the match suffix equality check first.
Only rejection in the affected symbol execution proof counts. Resource
failures are inconclusive. The actual translation is changed in scratch.
"""
from pathlib import Path
import os
import re
import shutil
import subprocess
import sys
import tempfile


def main():
    root = Path(__file__).resolve().parents[2]
    lake = shutil.which('lake') or str(Path.home() / '.elan/bin/lake')
    source = Path('ZlibF/Zlib/trees.c.lean')
    fragments = Path('ZlibF/Proof/trees.c.compress-source.lean')
    match = Path('ZlibF/Proof/trees.c.compress-match.lean')
    originals = {p: (root / p).read_text() for p in (source, fragments, match)}
    cases = (
        ('length-subtraction',
         'isub lc (← Ptr.index (.ref .st_base_length 0 : IPtr) code.toNat)',
         'iadd lc (← Ptr.index (.ref .st_base_length 0 : IPtr) code.toNat)',
         None, None, 'cbLengthExtra_run'),
        ('length-width', 'send_bits s lc extra', 'send_bits s lc 1',
         None, None, 'cbLengthExtra_run'),
        ('distance-decrement', 'let dist := dist - 1', 'let dist := dist',
         None, None, 'cbDistance_run'),
        ('distance-subtraction',
         'dist - (i2u (← Ptr.index (.ref .st_base_dist 0 : IPtr) code.toNat))',
         'dist + (i2u (← Ptr.index (.ref .st_base_dist 0 : IPtr) code.toNat))',
         None, None, 'cbDistance_run'),
        ('length-code-index',
         'send_code s (code + (i2u LITERALS) + 1).toNat ltree',
         'send_code s (code + (i2u LITERALS) + 0).toNat ltree',
         'send_code s (code + i2u LITERALS + 1).toNat ltree',
         'send_code s (code + i2u LITERALS + 0).toNat ltree', 'cbMatchSymbol_run'),
    )
    selected = set(sys.argv[1:])
    if selected:
        unknown = selected - {x[0] for x in cases}
        if unknown:
            raise RuntimeError('unknown mutation labels: ' + ', '.join(sorted(unknown)))
        cases = tuple(x for x in cases if x[0] in selected)

    def declaration(text, anchor):
        start = text.index(anchor)
        end = text.find('\n/--', start)
        if end < 0:
            end = text.index('\nend Zlib.Trees.Proofs', start)
        return text[start:end]

    def gate(text):
        return ('import ZlibF.Proof.«trees.c.compress-source»\n'
                'namespace Zlib.Trees.Proofs\nopen C Zlib.Trees Out\n'
                'set_option maxRecDepth 10000\n' +
                declaration(text, 'def cbDistance ') + '\n' +
                declaration(text, 'def cbLengthExtra ') + '\n' +
                declaration(text, 'theorem cbSymbol_match_source ') + '\nend Zlib.Trees.Proofs\n')

    with tempfile.TemporaryDirectory(prefix='trees-compress-matches-') as directory:
        scratch = Path(directory)
        for name in ('lakefile.toml', 'lean-toolchain'):
            shutil.copy2(root / name, scratch / name)
        shutil.copytree(root / 'ZlibF', scratch / 'ZlibF')
        shutil.copytree(root / '.lake/build', scratch / '.lake/build')

        def run(args):
            return subprocess.run([lake, *args], cwd=scratch, env=dict(os.environ, LC_ALL='C'),
                                  text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=600)

        def require(result, label):
            if result.returncode:
                raise RuntimeError(label + ':\n' + result.stdout)

        module = os.environ.get('ZLIBF_PAYLOAD_CALLER', 'ZlibF.Proof.«trees.c.compress-fixed»')
        require(run(['build', module]), 'positive complete fixed literal/match baseline')
        print('baseline: ' + module + ' checks', flush=True)
        for label, old, new, helper_old, helper_new, theorem in cases:
            left, body = originals[source].split('def compress_block (', 1)
            body, right = body.split('/-- `local int detect_data_type', 1)
            if body.count(old) != 1 or originals[fragments].count(old) != 1:
                raise RuntimeError('ambiguous source mutation: ' + label)
            (scratch / source).write_text(left + 'def compress_block (' + body.replace(old, new)
                                         + '/-- `local int detect_data_type' + right)
            (scratch / fragments).write_text(originals[fragments].replace(old, new))
            helper_old = helper_old or old
            helper_new = helper_new or new
            changed = originals[match]
            if changed.count(helper_old) != 1:
                raise RuntimeError('ambiguous suffix mutation: ' + label)
            changed = changed.replace(helper_old, helper_new)
            (scratch / match).write_text(changed)
            require(run(['build', 'ZlibF.Zlib.«trees.c»']), label + ' actual source compilation')
            require(run(['build', 'ZlibF.Proof.«trees.c.compress-source»']), label + ' complete source equality')
            check = scratch / '.lake/mutated-payload-source.lean'
            check.write_text(gate(changed))
            require(run(['env', 'lean', str(check)]), label + ' match suffix equality')
            result = run(['build', os.environ.get('ZLIBF_PAYLOAD_MUTATION_TARGET', 'ZlibF.Proof.«trees.c.compress-fixed»')])
            first = re.search(r'^error: ([^\n]+)', result.stdout, re.MULTILINE)
            hit = re.match(re.escape(str(match)) + r':(\d+):', first.group(1)) if first else None
            start = changed[:changed.index('theorem ' + theorem)].count('\n') + 1
            next_theorem = changed.find('\ntheorem ', changed.index('theorem ' + theorem) + len('theorem ' + theorem))
            end = len(changed.splitlines()) + 1 if next_theorem < 0 else changed[:next_theorem].count('\n') + 1
            exhausted = any(word in result.stdout.lower() for word in (
                'maximum recursion depth', 'maximum number of heartbeats', 'deep recursion detected',
                'deterministic timeout', 'interrupted', 'out of memory'))
            if result.returncode == 0 or hit is None or exhausted or not start <= int(hit.group(1)) < end:
                raise RuntimeError(label + ' survived or failed inconclusively:\n' + result.stdout)
            print('KILLED ' + label + ': ' + first.group(1) + '; complete and suffix source equalities check', flush=True)


if __name__ == '__main__':
    main()
