#!/usr/bin/env python3
"""Actual heapify/order proofs must reject synchronised source mutations."""
from pathlib import Path
import os
import re
import shutil
import subprocess
import tempfile


def main():
    root = Path(__file__).resolve().parents[2]
    source = Path('ZlibF/Zlib/trees.c.lean')
    heapify = Path('ZlibF/Proof/trees.c.build.heapify.lean')
    tail = Path('ZlibF/Proof/trees.c.build.order.lean')
    leaves = Path('ZlibF/Proof/trees.c.build.leaves.lean')
    originals = {p: (root / p).read_text() for p in (source, heapify, leaves, tail)}
    variants = (
        ('skipped-root', 'n.toInt ≥ 1', 'n.toInt > 1', 'ws_btHeapify'),
        ('dropped-sift-down', 'pqdownheap s tree n', 'pure ()', 'ws_btHeapify'),
        ('wrong-start-divisor', '((← rd s).heap_len / 2)', '((← rd s).heap_len / 3)', 'ws_btHeapify'),
        ('doubled-decrement', '(fun n => isub n 1)', '(fun n => isub n 2)', 'ws_btHeapify'),
        ('zero-descriptor-maximum',
         'stTreeDesc desc { (← ldTreeDesc desc) with max_code := mc }',
         'stTreeDesc desc { (← ldTreeDesc desc) with max_code := 0 }', 'ws_btOrder_leaf'),
    )
    env = os.environ.copy()
    env['LC_ALL'] = 'C'

    def run(where, args):
        return subprocess.run(args, cwd=where, env=env, text=True,
                              stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=600)

    def build(where):
        return run(where, ['lake', 'build', 'ZlibF.Proof.«trees.c.build.order»'])

    def heap_header(text):
        prefix = text.split('/-- Every leaf representation fact', 1)[0]
        order = 'def btOrder' + text.split('def btOrder', 1)[1].split('/-- The maximum-symbol write', 1)[0]
        return prefix + order + '\nend Zlib.Trees.Proofs\n'

    with tempfile.TemporaryDirectory(prefix='trees-heapify-') as name:
        scratch = Path(name)
        for f in ('lakefile.toml', 'lean-toolchain'):
            shutil.copy2(root / f, scratch / f)
        shutil.copytree(root / 'ZlibF', scratch / 'ZlibF')
        shutil.copytree(root / '.lake', scratch / '.lake')
        baseline = build(scratch)
        if baseline.returncode:
            raise RuntimeError('baseline failed:\n' + baseline.stdout)
        for label, old, new, theorem in variants:
            for path, original in originals.items():
                text = original
                if path == source:
                    left, body = original.split('def build_tree (', 1)
                    before, body = body.split('  -- desc->max_code = max_code;', 1)
                    middle, after = body.split('  -- node = elems;', 1)
                    old_source = old.replace('max_code := mc', 'max_code := max_code') if label == 'zero-descriptor-maximum' else old
                    if middle.count(old_source) != 1:
                        raise RuntimeError('ambiguous actual mutation: ' + label)
                    text = left + 'def build_tree (' + before + '  -- desc->max_code = max_code;' + middle.replace(old_source, new) + '  -- node = elems;' + after
                elif path == leaves:
                    old_source = old.replace('max_code := mc', 'max_code := max_code') if label == 'zero-descriptor-maximum' else old
                    if original.count(old_source) != 1:
                        raise RuntimeError('ambiguous parent source fragment: ' + label)
                    text = original.replace(old_source, new)
                elif path == heapify:
                    if theorem == 'ws_btHeapify':
                        prefix, rest = original.split('/-- Every leaf representation fact', 1)
                        if prefix.count(old) != 1:
                            raise RuntimeError('ambiguous heapify fragment: ' + label)
                        text = prefix.replace(old, new) + '/-- Every leaf representation fact' + rest
                    else:
                        if original.count(old) != 1:
                            raise RuntimeError('ambiguous descriptor fragment: ' + label)
                        text = original.replace(old, new)
                    text = text.replace('namespace Zlib.Trees.Proofs', 'set_option maxHeartbeats 2000000\n\nnamespace Zlib.Trees.Proofs', 1)
                (scratch / path).write_text(text)
            changed = (scratch / heapify).read_text()
            start = changed[:changed.index('theorem ' + theorem)].count('\n') + 1
            marker = 'theorem ws_btHeapify_leaf' if theorem == 'ws_btHeapify' else 'theorem BTScanInv.desc_heap_max'
            end = changed[:changed.index(marker)].count('\n') + 1
            result = build(scratch)
            first = re.search(r'^error: ([^\n]+)', result.stdout, re.MULTILINE)
            hit = re.match(re.escape(str(heapify)) + r':(\d+):', first.group(1)) if first else None
            exhausted = first and any(x in first.group(1).lower() for x in ('timeout', 'heartbeats', 'recursion depth'))
            if result.returncode == 0 or hit is None or not start <= int(hit.group(1)) < end or exhausted:
                raise RuntimeError('mutant survived or failed outside its function proof:\n' + result.stdout)
            (scratch / heapify).write_text(heap_header(changed))
            changed_tail = (scratch / tail).read_text()
            (scratch / tail).write_text(changed_tail.split('/-- The complete actual prefix before merging', 1)[0] + '\nend Zlib.Trees.Proofs\n')
            checked = build(scratch)
            if checked.returncode:
                raise RuntimeError('synchronised complete source equality failed:\n' + checked.stdout)
            print('KILLED ' + label + ': ' + first.group(1) + '; build_tree_eq_order still checks', flush=True)


if __name__ == '__main__':
    main()
