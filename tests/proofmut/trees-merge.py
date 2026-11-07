#!/usr/bin/env python3
"""Merge proofs reject all mutations while independent complete source equality survives."""
from pathlib import Path
import os
import re
import shutil
import subprocess
import tempfile


def main():
    root = Path(__file__).resolve().parents[2]
    source = Path('ZlibF/Zlib/trees.c.lean')
    merge = Path('ZlibF/Proof/trees.c.build.merge.lean')
    tail = Path('ZlibF/Proof/trees.c.build.tail.lean')
    leaves = Path('ZlibF/Proof/trees.c.build.leaves.lean')
    order = Path('ZlibF/Proof/trees.c.build.order.lean')
    scan = Path('ZlibF/Proof/trees.c.build.scan.lean')
    force = Path('ZlibF/Proof/trees.c.build.force.lean')
    heapify = Path('ZlibF/Proof/trees.c.build.heapify.lean')
    originals = {p: (root / p).read_text() for p in (source, merge, tail, leaves, order, scan, force, heapify)}
    variants = (
        ('wrong-second-root', 'btPick2', 'let m ← heapAt s 1', 'let m ← heapAt s 2', 'ws_btPick2'),
        ('lost-first-child', 'btKeepChildren', 'heapSet s hm n', 'heapSet s hm m', 'ws_btKeepChildren'),
        ('doubled-tail-decrement', 'btKeepChildren', 'isub (← rd s).heap_max 1', 'isub (← rd s).heap_max 2', 'ws_btKeepChildren'),
        ('lost-second-frequency', 'btSetFreq', 'setFc tree node.toInt (fn + fm)', 'setFc tree node.toInt fn', 'ws_btSetFreq'),
        ('reversed-depth-comparison', 'btSetDepth', 'if dn ≥ dm then', 'if dn ≤ dm then', 'ws_btSetDepth'),
        ('wrong-selected-depth-read', 'btSetDepth',
         'if dn ≥ dm then Ptr.index dp n.toInt else Ptr.index dp m.toInt',
         'if dn ≥ dm then Ptr.index dp m.toInt else Ptr.index dp m.toInt', 'ws_btSetDepth'),
        ('doubled-parent-depth', 'btSetDepth', 'setAt dp node.toInt (mx + 1)', 'setAt dp node.toInt (mx + 2)', 'ws_btSetDepth'),
        ('missing-second-parent', 'btSetParents', 'setDl tree m.toInt (i2us node)', 'pure ()', 'ws_btSetParents'),
        ('wrong-first-parent', 'btSetParents', 'setDl tree n.toInt (i2us node)', 'setDl tree n.toInt (i2us n)', 'ws_btSetParents'),
        ('zero-new-root', 'btMergeClose', 'heapSet s 1 node', 'heapSet s 1 0', 'ws_btMergeClose'),
        ('doubled-node-increment', 'btMergeClose', 'let node\' ← iadd node 1', 'let node\' ← iadd node 2', 'ws_btMergeClose'),
        ('missing-final-sift', 'btMergeClose', 'pqdownheap s tree 1', 'pure ()', 'ws_btMergeClose'),
        ('premature-merge-stop', 'btMergeLoop', 'heap_len.toInt ≥ 2', 'heap_len.toInt ≥ 3', 'ws_btMergeLoop'),
        ('extra-merge-iteration', 'btMergeLoop', 'heap_len.toInt ≥ 2', 'heap_len.toInt ≥ 1', 'ws_btMergeLoop'),
        ('wrong-saved-root', 'btSaveRoot', 'let top ← heapAt s 1', 'let top ← heapAt s 2', 'ws_btSaveRoot'),
        ('doubled-final-decrement', 'btSaveRoot', 'isub (← rd s).heap_max 1', 'isub (← rd s).heap_max 2', 'ws_btSaveRoot'),
        ('missing-final-root-store', 'btSaveRoot', 'heapSet s hm top', 'pure ()', 'ws_btSaveRoot'),
    )
    env = os.environ.copy()
    env['LC_ALL'] = 'C'

    def run(where, args):
        return subprocess.run(args, cwd=where, env=env, text=True,
                              stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=600)

    def build(where, baseline=False):
        target = 'ZlibF.Proof.«trees.c.build.tail»' if baseline else 'ZlibF.Proof.«trees.c.build.merge»'
        return run(where, ['lake', 'build', target])

    def section(text, first, last):
        return first + text.split(first, 1)[1].split(last, 1)[0]

    def source_equality(scratch):
        blocks = [
            section((scratch / scan).read_text(), '/-- The first scan\'s body', '/-- Exact state frame'),
            section((scratch / force).read_text(), '/-- The body of the two-leaf repair', '/-- A static tree is absent'),
            section((scratch / heapify).read_text(), '/-- The actual descending', '/-- Every leaf representation fact'),
            section((scratch / heapify).read_text(), '/-- The actual descriptor read/store', '/-- The maximum-symbol write'),
            section((scratch / leaves).read_text(), '/-- The actual descriptor reads', '/-- The unchanged main suffix'),
            section((scratch / order).read_text(), '/-- Actual leaf preparation, descriptor', '/-- The current source suffix'),
        ]
        merged = (scratch / merge).read_text().split('/-- The actual removal followed', 1)[0].split('namespace Zlib.Trees.Proofs', 1)[1]
        finished = (scratch / tail).read_text().split('/-- The actual descriptor/reset/scan/repair/heapify prefix and full merging', 1)[0].split('namespace Zlib.Trees.Proofs', 1)[1]
        finished = finished.replace('open C Zlib.Trees Zlib.Trees.Proofs.GB', 'open C Zlib.Trees')
        text = ('import ZlibF.Zlib.«trees.c»\nimport ZlibF.Proof.«trees.c.monad»\n\nnamespace Zlib.Trees.Proofs\nopen C Zlib.Trees\n'
                + '\n'.join(blocks) + merged + finished + '\nend Zlib.Trees.Proofs\n')
        (scratch / 'SourceEquality.lean').write_text(text)
        return run(scratch, ['lake', 'env', 'lean', 'SourceEquality.lean'])

    with tempfile.TemporaryDirectory(prefix='trees-merge-') as name:
        scratch = Path(name)
        for f in ('lakefile.toml', 'lean-toolchain'):
            shutil.copy2(root / f, scratch / f)
        shutil.copytree(root / 'ZlibF', scratch / 'ZlibF')
        shutil.copytree(root / '.lake', scratch / '.lake')
        baseline = build(scratch, baseline=True)
        if baseline.returncode:
            raise RuntimeError('baseline failed:\n' + baseline.stdout)
        for label, fragment, old, new, theorem in variants:
            first_marker = '  -- s->heap[--(s->heap_max)] = s->heap[SMALLEST];' if fragment == 'btSaveRoot' else '  -- node = elems;'
            last_marker = '  -- gen_bitlen(s, (tree_desc *)desc);' if fragment == 'btSaveRoot' else '  -- s->heap[--(s->heap_max)] = s->heap[SMALLEST];'
            expected = 2 if label == 'doubled-tail-decrement' else 1
            for path, original in originals.items():
                text = original
                if path in (source, leaves, order):
                    before, body = original.split(first_marker, 1)
                    body, after = body.split(last_marker, 1)
                    if body.count(old) != expected:
                        raise RuntimeError('ambiguous actual/parent source mutation: ' + label)
                    text = before + first_marker + body.replace(old, new) + last_marker + after
                elif path == merge:
                    before, body = original.split('def ' + fragment + ' ', 1)
                    body, after = body.split('\n\n/--', 1)
                    if body.count(old) != expected:
                        raise RuntimeError('ambiguous named mutation: ' + label)
                    text = before + 'def ' + fragment + ' ' + body.replace(old, new) + '\n\n/--' + after
                    text = text.replace('namespace Zlib.Trees.Proofs',
                                        'set_option maxHeartbeats 2000000\n\nnamespace Zlib.Trees.Proofs', 1)
                (scratch / path).write_text(text)
            changed = (scratch / merge).read_text()
            start_offset = changed.index('theorem ' + theorem)
            end_offset = changed.find('\n/--', start_offset)
            if end_offset < 0:
                end_offset = len(changed)
            start = changed[:start_offset].count('\n') + 1
            end = changed[:end_offset].count('\n') + 1
            result = build(scratch)
            first = re.search(r'^error: ([^\n]+)', result.stdout, re.MULTILINE)
            hit = re.match(re.escape(str(merge)) + r':(\d+):', first.group(1)) if first else None
            exhausted = first and any(x in first.group(1).lower() for x in ('timeout', 'heartbeats', 'recursion depth'))
            if result.returncode == 0 or hit is None or not start <= int(hit.group(1)) < end or exhausted:
                raise RuntimeError('mutant survived or failed outside its execution proof:\n' + result.stdout)
            checked = source_equality(scratch)
            if checked.returncode:
                raise RuntimeError('independent complete source equality failed:\n' + checked.stdout)
            print('KILLED ' + label + ': ' + first.group(1) + '; build_tree_eq_heap_codes still checks independently', flush=True)


if __name__ == '__main__':
    main()
