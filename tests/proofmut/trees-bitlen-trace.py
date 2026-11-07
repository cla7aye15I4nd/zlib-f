#!/usr/bin/env python3
"""Reject source repair mutations with complete gen_bitlen stage refinement.

Translation and named fragments change together. The complete source equality
must check independently. Only a local execution-proof error kills a mutant;
resource exhaustion and unrelated errors fail the check.
"""
from pathlib import Path
import os
import re
import shutil
import subprocess
import tempfile


def main():
    root = Path(__file__).resolve().parents[2]
    source = Path('ZlibF/Zlib/trees.c.lean')
    fragment = Path('ZlibF/Proof/trees.c.heap.gbdef.lean')
    originals = {p: (root / p).read_text() for p in (source, fragment)}
    variants = [
        ('overflow-decrement', 'isub overflow 2', 'isub overflow 1',
         'trees.c.heap.gbfix', 'ws_gbFixRound', 'ws_gbFixLoop'),
        ('split-count', 'setAt bc b1.toInt ((← Ptr.index bc b1.toInt) + 2)',
         'setAt bc b1.toInt ((← Ptr.index bc b1.toInt) + 1)',
         'trees.c.heap.gbfix', 'ws_gbFixRound', 'ws_gbFixLoop'),
        ('assigned-length', 'setDl tree m.toInt (i2us bits)',
         'setDl tree m.toInt (i2us (← iadd bits 1))',
         'trees.c.heap.gbre', 'ws_gbInner', 'bne_zero_iff'),
    ]
    env = os.environ.copy()
    env['LC_ALL'] = 'C'

    def run(where, target):
        return subprocess.run(['lake', 'build', target], cwd=where, env=env,
                              text=True, stdout=subprocess.PIPE,
                              stderr=subprocess.STDOUT, timeout=180)

    def require_success(result, label):
        if result.returncode:
            raise RuntimeError(label + ':\n' + result.stdout)

    with tempfile.TemporaryDirectory(prefix='trees-bitlen-trace-') as name:
        scratch = Path(name)
        for file in ('lakefile.toml', 'lean-toolchain'):
            shutil.copy2(root / file, scratch / file)
        shutil.copytree(root / 'ZlibF', scratch / 'ZlibF')
        shutil.copytree(root / '.lake', scratch / '.lake')
        target = 'ZlibF.Proof.«trees.c.heap.gbtrace-order»'
        require_success(run(scratch, target), 'complete gen_bitlen baseline failed')
        print('baseline: complete gen_bitlen stage/order refinement checks', flush=True)
        for label, old, new, module, first_theorem, last_theorem in variants:
            proof = Path('ZlibF/Proof/' + module + '.lean')
            text = (root / proof).read_text()
            start = text[:text.index('theorem ' + first_theorem)].count('\n') + 1
            end = text[:text.index('theorem ' + last_theorem)].count('\n') + 1
            for file, content in originals.items():
                if content.count(old) != 1:
                    raise RuntimeError('ambiguous mutation in ' + str(file))
                (scratch / file).write_text(content.replace(old, new))
            require_success(run(scratch, 'ZlibF.Proof.«trees.c.heap.gbdef»'),
                            label + ': synchronized whole-source equality failed')
            result = run(scratch, target)
            first = re.search(r'^error: ([^\n]+)', result.stdout, re.MULTILINE)
            hit = re.match(re.escape(str(proof)) + r':(\d+):', first.group(1)) if first else None
            exhausted = any(word in result.stdout.lower() for word in
                            ('maximum recursion depth', 'maximum number of heartbeats',
                             'deterministic timeout', 'interrupted', 'out of memory'))
            if result.returncode == 0 or hit is None or not start <= int(hit.group(1)) < end or exhausted:
                raise RuntimeError(label + ': survived or failed outside the matching execution proof:\n' + result.stdout)
            print('KILLED ' + label + ': ' + first.group(1)
                  + '; complete source equality checks; no resource timeout', flush=True)


if __name__ == '__main__':
    main()
