#!/usr/bin/env python3
"""Dynamic tag mutations must fail emission while complete source equality checks."""
from pathlib import Path
import os
import re
import shutil
import subprocess
import tempfile


def main():
    root = Path(__file__).resolve().parents[2]
    source = Path('ZlibF/Zlib/trees.c.lean')
    flush = Path('ZlibF/Proof/trees.c.flush-source.lean')
    prepare = Path('ZlibF/Proof/deflate.c.engine.block-prepare.lean')
    header = Path('ZlibF/Proof/trees.c.dynamic-header.lean')
    originals = {p: (root / p).read_text() for p in (source, flush, prepare, header)}
    tag = 'send_bits s (← iadd (DYN_TREES <<< 1) last) 3'
    variants = (
        ('dropped-dynamic-tag', 'pure ()'),
        ('narrow-dynamic-tag', tag[:-1] + '2'),
        ('wrong-dynamic-type', tag.replace('DYN_TREES', 'STATIC_TREES')),
    )
    env = os.environ.copy()
    env['LC_ALL'] = 'C'

    def build(where, target):
        return subprocess.run(['lake', 'build', target], cwd=where, env=env, text=True,
                              stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=300)

    with tempfile.TemporaryDirectory(prefix='trees-dynamic-header-') as name:
        scratch = Path(name)
        for filename in ('lakefile.toml', 'lean-toolchain'):
            shutil.copy2(root / filename, scratch / filename)
        shutil.copytree(root / 'ZlibF', scratch / 'ZlibF')
        shutil.copytree(root / '.lake', scratch / '.lake')
        target = 'ZlibF.Proof.«deflate.c.engine.dynamic-header»'
        baseline = build(scratch, target)
        if baseline.returncode:
            raise RuntimeError('baseline failed:\n' + baseline.stdout)
        print('baseline: actual dynamic header, original symbols and derived payload room check', flush=True)
        for label, replacement in variants:
            for path, original in originals.items():
                old, new = tag, replacement
                if path == prepare:
                    old = old.replace('← iadd', '← Zlib.Trees.iadd')
                    new = new.replace('← iadd', '← Zlib.Trees.iadd')
                if original.count(old) != 1:
                    raise RuntimeError('ambiguous mutation in ' + str(path))
                (scratch / path).write_text(original.replace(old, new))
            changed = (scratch / header).read_text()
            cut = changed.split('/-- The real dynamic tag and all three count arguments', 1)[0]
            (scratch / header).write_text(cut + '\nend Zlib.Trees.Proofs\n')
            equality = build(scratch, 'ZlibF.Proof.«trees.c.dynamic-header»')
            if equality.returncode:
                raise RuntimeError('complete synchronized flush source equality failed:\n' + equality.stdout)
            (scratch / header).write_text(changed)
            first_line = changed[:changed.index('theorem dynamic_block_header_emit')].count('\n') + 1
            last_line = changed[:changed.index('\nend Zlib.Trees.Proofs')].count('\n') + 1
            # The complete caller is checked above. A mutated source only
            # needs its matching function proof here; unrelated engine
            # rebuilds do not strengthen the rejection evidence.
            result = build(scratch, 'ZlibF.Proof.«trees.c.dynamic-header»')
            first = re.search(r'^error: ([^\n]+)', result.stdout, re.MULTILINE)
            hit = re.match(re.escape(str(header)) + r':(\d+):', first.group(1)) if first else None
            exhausted = any(word in result.stdout.lower() for word in
                            ('maximum recursion depth', 'maximum number of heartbeats',
                             'deterministic timeout', 'out of memory', 'interrupted'))
            if result.returncode == 0 or hit is None or not first_line <= int(hit.group(1)) < last_line or exhausted:
                raise RuntimeError('mutant survived or failed outside header execution proof:\n' + result.stdout)
            print('KILLED ' + label + ': ' + first.group(1)
                  + '; complete flush source equality still checks; no resource failure', flush=True)


if __name__ == '__main__':
    main()
