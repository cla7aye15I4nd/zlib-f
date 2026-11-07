#!/usr/bin/env python3
"""Actual tally mutations must fail execution proofs, with source equality intact."""
from pathlib import Path
import os
import re
import shutil
import subprocess
import tempfile


def main():
    root = Path(__file__).resolve().parents[2]
    source = Path('ZlibF/Zlib/trees.c.lean')
    proof = Path('ZlibF/Proof/trees.c.tally.lean')
    originals = {p: (root / p).read_text() for p in (source, proof)}
    variants = (
        ('literal-counts-end-block',
         'setFc lt lc.toNat ((← getFc lt lc.toNat) + 1)',
         'setFc lt (lc.toNat + 1) ((← getFc lt (lc.toNat + 1)) + 1)',
         'tallyTail_lit', 'theorem LITERALS_toInt'),
        ('match-counts-end-block',
         'let idx := (u8i lcode).toInt + LITERALS.toInt + 1',
         'let idx := LITERALS.toInt',
         'tallyTail_match', '@[simp] theorem bumpFc_size'),
        ('wrong-full-flag',
         'return (if d.sym_next == d.sym_end then 1 else 0)',
         'return (if d.sym_next + 1 == d.sym_end then 1 else 0)',
         'tallyTail_lit', 'theorem LITERALS_toInt'),
    )
    env = os.environ.copy()
    env['LC_ALL'] = 'C'

    def run(where, args):
        return subprocess.run(args, cwd=where, env=env, text=True,
                              stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=600)

    def build(where):
        return run(where, ['lake', 'build', 'ZlibF.Proof.«trees.c.tally-support»'])

    with tempfile.TemporaryDirectory(prefix='trees-tally-support-') as name:
        scratch = Path(name)
        for file in ('lakefile.toml', 'lean-toolchain'):
            shutil.copy2(root / file, scratch / file)
        shutil.copytree(root / 'ZlibF', scratch / 'ZlibF')
        shutil.copytree(root / '.lake', scratch / '.lake')
        baseline = build(scratch)
        if baseline.returncode:
            raise RuntimeError('baseline failed:\n' + baseline.stdout)
        print('baseline: initialization, valid tally sequence and header fields check', flush=True)
        for label, old, new, theorem, end_marker in variants:
            left, body = originals[source].split('def «_tr_tally» (', 1)
            body, right = body.split('\nend Zlib.Trees', 1)
            if body.count(old) != 1:
                raise RuntimeError('ambiguous actual mutation: ' + label)
            (scratch / source).write_text(left + 'def «_tr_tally» (' + body.replace(old, new)
                                         + '\nend Zlib.Trees' + right)
            left, body = originals[proof].split('def tallyTail (', 1)
            body, right = body.split('\ntheorem tally_split', 1)
            if body.count(old) != 1:
                raise RuntimeError('ambiguous named mutation: ' + label)
            changed = left + 'def tallyTail (' + body.replace(old, new) + '\ntheorem tally_split' + right
            (scratch / proof).write_text(changed)
            start = changed[:changed.index('theorem ' + theorem)].count('\n') + 1
            end = changed[:changed.index(end_marker)].count('\n') + 1
            result = build(scratch)
            first = re.search(r'^error: ([^\n]+)', result.stdout, re.MULTILINE)
            hit = re.match(re.escape(str(proof)) + r':(\d+):', first.group(1)) if first else None
            exhausted = any(word in result.stdout.lower()
                            for word in ('maximum recursion depth', 'maximum number of heartbeats',
                                         'deterministic timeout'))
            if result.returncode == 0 or hit is None or not start <= int(hit.group(1)) < end or exhausted:
                raise RuntimeError('mutant survived or failed outside its tally execution proof:\n' + result.stdout)
            cutpoint = changed.split('theorem tallyTail_lit', 1)[0] + '\nend Zlib.Trees.Proofs.Out\n'
            (scratch / 'TallyCutpoint.lean').write_text(cutpoint)
            checked = run(scratch, ['lake', 'env', 'lean', 'TallyCutpoint.lean'])
            if checked.returncode:
                raise RuntimeError('synchronized whole-function equality failed:\n' + checked.stdout)
            print('KILLED ' + label + ': ' + first.group(1) + '; tally_split still checks', flush=True)


if __name__ == '__main__':
    main()
