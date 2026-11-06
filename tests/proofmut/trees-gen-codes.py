#!/usr/bin/env python3
"""Canonical assignment mutants must fail the actual gen_codes loop proofs."""
from pathlib import Path
import os
import re
import shutil
import subprocess
import tempfile


def main():
    root = Path(__file__).resolve().parents[2]
    source = Path('ZlibF/Zlib/trees.c.lean')
    proof = Path('ZlibF/Proof/trees.c.codes.lean')
    originals = {p: (root / p).read_text() for p in (source, proof)}
    mutants = (
        ('wrong-start-shift',
         'let code := (code + b.toUInt32) <<< 1',
         'let code := (code + b.toUInt32) <<< 2', 'gcStart_run'),
        ('skipped-code',
         'let nc := nc.set! li (old + 1)',
         'let nc := nc.set! li (old + 2)', 'gcAssign_run'),
        ('zero-code-store',
         'setFc tree n.toInt r.toUInt16',
         'setFc tree n.toInt 0', 'gcAssign_run'),
    )
    env = os.environ.copy()
    env['LC_ALL'] = 'C'

    def run(where, args):
        return subprocess.run(args, cwd=where, env=env, text=True,
                              stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=600)

    def build(where):
        return run(where, ['lake', 'build', 'ZlibF.Proof.«trees.c.codes»'])

    with tempfile.TemporaryDirectory(prefix='trees-gen-codes-') as name:
        scratch = Path(name)
        for f in ('lakefile.toml', 'lean-toolchain'):
            shutil.copy2(root / f, scratch / f)
        shutil.copytree(root / 'ZlibF', scratch / 'ZlibF')
        shutil.copytree(root / '.lake', scratch / '.lake')
        baseline = build(scratch)
        if baseline.returncode:
            raise RuntimeError('baseline failed:\n' + baseline.stdout)
        for label, old, new, theorem in mutants:
            for path, original in originals.items():
                if path == source:
                    left, body = original.split('def gen_codes (', 1)
                    middle, right = body.split('def tr_static_init', 1)
                    if middle.count(old) != 1:
                        raise RuntimeError('ambiguous actual mutation: ' + label)
                    text = left + 'def gen_codes (' + middle.replace(old, new) + 'def tr_static_init' + right
                else:
                    left, right = original.split('/-- All fifteen canonical', 1)
                    if left.count(old) != 1:
                        raise RuntimeError('ambiguous cut-point mutation: ' + label)
                    text = left.replace(old, new) + '/-- All fifteen canonical' + right
                (scratch / path).write_text(text)
            changed_proof = (scratch / proof).read_text()
            start = changed_proof[:changed_proof.index('theorem ' + theorem)].count('\n') + 1
            end_marker = 'private theorem gc_reverse_eq' if theorem == 'gcStart_run' else 'theorem ws_gen_codes'
            end = changed_proof[:changed_proof.index(end_marker)].count('\n') + 1
            result = build(scratch)
            error = re.search(r'^error: ' + re.escape(str(proof)) + r':(\d+):[^\n]*', result.stdout, re.MULTILINE)
            exhausted = error and any(x in error.group(0) for x in ('timeout', 'heartbeats', 'recursion depth'))
            if result.returncode == 0 or error is None or not start <= int(error.group(1)) < end or exhausted:
                raise RuntimeError('mutant survived or failed outside its execution proof:\n' + result.stdout)
            cutpoint = changed_proof.split('/-- All fifteen canonical', 1)[0] + '\nend Zlib.Trees.Proofs\n'
            (scratch / 'Cutpoint.lean').write_text(cutpoint)
            checked = run(scratch, ['lake', 'env', 'lean', 'Cutpoint.lean'])
            if checked.returncode:
                raise RuntimeError('synchronised source equality failed:\n' + checked.stdout)
            print('KILLED ' + label + ': ' + error.group(0) + '; gen_codes_eq still checks', flush=True)


if __name__ == '__main__':
    main()
