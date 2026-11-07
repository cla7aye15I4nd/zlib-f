#!/usr/bin/env python3
"""Scan/reset mutations must fail execution proofs, with full source equality retained."""
from pathlib import Path
import os
import re
import shutil
import subprocess
import tempfile


def main():
    root = Path(__file__).resolve().parents[2]
    source = Path('ZlibF/Zlib/trees.c.lean')
    scan = Path('ZlibF/Proof/trees.c.build.scan.lean')
    force = Path('ZlibF/Proof/trees.c.build.force.lean')
    leaves = Path('ZlibF/Proof/trees.c.build.leaves.lean')
    originals = {p: (root / p).read_text() for p in (source, scan, force, leaves)}
    variants = (
        ('dropped-leaf-store', 'heapSet s hl n', 'pure ()', scan, 'btScanBody_used', '/-- One actual zero-frequency'),
        ('wrong-unused-length', 'setDl tree n.toInt 0', 'setDl tree n.toInt 1', scan, 'btScanBody_unused', '/-- Frequencies before'),
        ('wrong-maximum', 'pure (n, n)', 'pure (n, mc)', scan, 'btScanBody_used', '/-- One actual zero-frequency'),
        ('nonzero-heap-reset', 'heap_len := 0', 'heap_len := 1', leaves, 'ws_btScanStart', '/-- The actual descriptor/reset/scan/repair prefix'),
        ('wrong-heap-tail-reset', 'heap_max := HEAP_SIZE', 'heap_max := 0', leaves, 'ws_btScanStart', '/-- The actual descriptor/reset/scan/repair prefix'),
    )
    env = os.environ.copy()
    env['LC_ALL'] = 'C'

    def run(where, args):
        return subprocess.run(args, cwd=where, env=env, text=True,
                              stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=600)

    def build(where, module):
        return run(where, ['lake', 'build', module])

    with tempfile.TemporaryDirectory(prefix='trees-build-leaves-') as name:
        scratch = Path(name)
        for f in ('lakefile.toml', 'lean-toolchain'):
            shutil.copy2(root / f, scratch / f)
        shutil.copytree(root / 'ZlibF', scratch / 'ZlibF')
        shutil.copytree(root / '.lake', scratch / '.lake')
        baseline = build(scratch, 'ZlibF.Proof.«trees.c.build.leaves»')
        if baseline.returncode:
            raise RuntimeError('baseline failed:\n' + baseline.stdout)
        for label, old, new, proof, theorem, marker in variants:
            for path, original in originals.items():
                text = original
                if path == source:
                    before, body = original.split('def build_tree (', 1)
                    middle, after = body.split('  -- while (s->heap_len < 2) { ... }', 1)
                    if middle.count(old) != 1:
                        raise RuntimeError('ambiguous actual mutation: ' + label)
                    text = before + 'def build_tree (' + middle.replace(old, new) + '  -- while (s->heap_len < 2) { ... }' + after
                elif path == proof:
                    split = '/-- Exact state frame' if proof == scan else '/-- The actual start of'
                    before, after = original.split(split, 1)
                    if before.count(old) != 1:
                        raise RuntimeError('ambiguous named mutation: ' + label)
                    text = before.replace(old, new) + split + after
                (scratch / path).write_text(text)
            changed = (scratch / proof).read_text()
            start = changed[:changed.index('theorem ' + theorem)].count('\n') + 1
            end = changed[:changed.index(marker)].count('\n') + 1
            module = 'ZlibF.Proof.«trees.c.build.scan»' if proof == scan else 'ZlibF.Proof.«trees.c.build.leaves»'
            result = build(scratch, module)
            first = re.search(r'^error: ([^\n]+)', result.stdout, re.MULTILINE)
            hit = re.match(re.escape(str(proof)) + r':(\d+):', first.group(1)) if first else None
            exhausted = first and any(x in first.group(1).lower() for x in ('heartbeats', 'timeout', 'recursion depth'))
            if result.returncode == 0 or hit is None or not start <= int(hit.group(1)) < end or exhausted:
                raise RuntimeError('mutant survived or failed outside its execution proof:\n' + result.stdout)
            scan_defs = (scratch / scan).read_text().split('/-- Exact state frame', 1)[0].split('namespace Zlib.Trees.Proofs', 1)[1]
            force_defs = (scratch / force).read_text().split('/-- The body of the two-leaf repair', 1)[1].split('/-- A static tree is absent', 1)[0]
            force_defs = '/-- The body of the two-leaf repair' + force_defs
            leaf_defs = (scratch / leaves).read_text().split('/-- The actual descriptor reads', 1)[1].split('/-- The actual start of', 1)[0]
            leaf_defs = '/-- The actual descriptor reads' + leaf_defs
            equality = ('import ZlibF.Zlib.«trees.c»\nimport ZlibF.Proof.«trees.c.monad»\n\nnamespace Zlib.Trees.Proofs\n'
                        + scan_defs + force_defs + leaf_defs + '\nend Zlib.Trees.Proofs\n')
            (scratch / 'SourceEquality.lean').write_text(equality)
            checked = run(scratch, ['lake', 'env', 'lean', 'SourceEquality.lean'])
            if checked.returncode:
                raise RuntimeError('independent complete source equality failed:\n' + checked.stdout)
            print('KILLED ' + label + ': ' + first.group(1) + '; build_tree_eq_leaves still checks', flush=True)


if __name__ == '__main__':
    main()
