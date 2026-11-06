#!/usr/bin/env python3
"""Actual send_code mutations must fail its emission proof."""
from pathlib import Path
import os
import re
import shutil
import subprocess
import tempfile


def main():
    root = Path(__file__).resolve().parents[2]
    source = Path('ZlibF/Zlib/trees.c.lean')
    proof = Path('ZlibF/Proof/trees.c.emit.lean')
    original = (root / source).read_text()
    prefix, body = original.split('def send_code (', 1)
    body, suffix = body.split('/-- `d_code(dist)`', 1)
    variants = (
        ('wrong-length-entry', 'getDl tree c', 'getDl tree (c + 1)'),
        ('length-as-code', 'getFc tree c', 'getDl tree c'),
        ('extra-output-bit', 'send_bits s code len', 'send_bits s code (len + 1)'),
    )
    text = (root / proof).read_text()
    start = text[:text.index('theorem send_code_emit')].count('\n') + 1
    end = text[:text.index('end Zlib.Trees.Proofs.Out')].count('\n') + 1
    env = os.environ.copy()
    env['LC_ALL'] = 'C'

    def build(where):
        return subprocess.run(
            ['lake', 'build', 'ZlibF.Proof.«trees.c.build.frame»'], cwd=where,
            env=env, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
            timeout=600,
        )

    with tempfile.TemporaryDirectory(prefix='trees-send-code-') as name:
        scratch = Path(name)
        for file in ('lakefile.toml', 'lean-toolchain'):
            shutil.copy2(root / file, scratch / file)
        shutil.copytree(root / 'ZlibF', scratch / 'ZlibF')
        shutil.copytree(root / '.lake', scratch / '.lake')
        baseline = build(scratch)
        if baseline.returncode:
            raise RuntimeError('baseline failed:\n' + baseline.stdout)
        print('baseline: complete construction, format and emission frame checks', flush=True)
        for label, old, new in variants:
            if body.count(old) != 1:
                raise RuntimeError('ambiguous send_code mutation: ' + label)
            changed = prefix + 'def send_code (' + body.replace(old, new) + '/-- `d_code(dist)`' + suffix
            (scratch / source).write_text(changed)
            result = build(scratch)
            first = re.search(r'^error: ([^\n]+)', result.stdout, re.MULTILINE)
            hit = re.match(re.escape(str(proof)) + r':(\d+):', first.group(1)) if first else None
            exhausted = any(word in result.stdout.lower()
                            for word in ('maximum recursion depth', 'maximum number of heartbeats',
                                         'deterministic timeout'))
            if result.returncode == 0 or hit is None or not start <= int(hit.group(1)) < end or exhausted:
                raise RuntimeError('mutant survived or failed outside send_code_emit:\n' + result.stdout)
            print('KILLED ' + label + ': ' + first.group(1), flush=True)


if __name__ == '__main__':
    main()
