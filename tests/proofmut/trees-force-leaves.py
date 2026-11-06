#!/usr/bin/env python3
"""Leaf repair mutants must fail execution while full source equality survives."""
from pathlib import Path
import os
import re
import shutil
import subprocess
import tempfile


def main():
    root = Path(__file__).resolve().parents[2]
    source = Path('ZlibF/Zlib/trees.c.lean')
    force = Path('ZlibF/Proof/trees.c.build.force.lean')
    leaves = Path('ZlibF/Proof/trees.c.build.leaves.lean')
    originals = {p: (root / p).read_text() for p in (source, force, leaves)}
    variants = (
        ('wrong-fresh-symbol', 'if mc.toInt < 2 then', 'if mc.toInt < 1 then', 'btForceBody_run'),
        ('zero-dummy-frequency', 'setFc tree node.toInt 1', 'setFc tree node.toInt 0', 'btForceBody_run'),
        ('doubled-leaf-increment', 'let hl ← iadd (← rd s).heap_len 1',
         'let hl ← iadd (← rd s).heap_len 2', 'btForceBody_run'),
        ('dropped-optimal-cost', 'md s fun d => { d with opt_len := d.opt_len - 1 }',
         'md s fun d => { d with opt_len := d.opt_len }', 'btForceBody_run'),
        ('dropped-static-cost', 'md s fun d => { d with static_len := d.static_len - l.toUInt64 }',
         'md s fun d => { d with static_len := d.static_len }', 'btForceBody_run'),
        ('three-leaf-guard', '((← rd s).heap_len.toInt < 2)',
         '((← rd s).heap_len.toInt < 3)', 'ws_btForce'),
    )
    env = os.environ.copy()
    env['LC_ALL'] = 'C'

    def run(where, args):
        return subprocess.run(args, cwd=where, env=env, text=True,
                              stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=600)

    def build(where):
        return run(where, ['lake', 'build', 'ZlibF.Proof.«trees.c.build.leaves»'])

    with tempfile.TemporaryDirectory(prefix='trees-force-leaves-') as name:
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
                    before, body = body.split('  -- while (s->heap_len < 2) { ... }', 1)
                    middle, right = body.split('  -- desc->max_code = max_code;', 1)
                    if middle.count(old) != 1:
                        raise RuntimeError('ambiguous actual mutation: ' + label)
                    text = left + 'def build_tree (' + before + '  -- while (s->heap_len < 2) { ... }' + middle.replace(old, new) + '  -- desc->max_code = max_code;' + right
                elif path == force:
                    prefix, rest = original.split('/-- A static tree is absent', 1)
                    if prefix.count(old) != 1:
                        raise RuntimeError('ambiguous named mutation: ' + label)
                    text = prefix.replace(old, new) + '/-- A static tree is absent' + rest
                    text = text.replace('namespace Zlib.Trees.Proofs', 'set_option maxHeartbeats 2000000\n\nnamespace Zlib.Trees.Proofs', 1)
                (scratch / path).write_text(text)
            changed = (scratch / force).read_text()
            start = changed[:changed.index('theorem ' + theorem)].count('\n') + 1
            marker = '@[simp] theorem btForceState_tree' if theorem == 'btForceBody_run' else 'theorem BTForceTrace.lengths'
            end = changed[:changed.index(marker)].count('\n') + 1
            result = build(scratch)
            first = re.search(r'^error: ([^\n]+)', result.stdout, re.MULTILINE)
            hit = re.match(re.escape(str(force)) + r':(\d+):', first.group(1)) if first else None
            exhausted = first and any(x in first.group(1).lower() for x in ('heartbeats', 'timeout', 'recursion depth'))
            if result.returncode == 0 or hit is None or not start <= int(hit.group(1)) < end or exhausted:
                raise RuntimeError('mutant survived or failed outside its execution proof:\n' + result.stdout)
            (scratch / force).write_text(changed.split('/-- A static tree is absent', 1)[0] + '\nend Zlib.Trees.Proofs\n')
            changed_leaves = (scratch / leaves).read_text()
            (scratch / leaves).write_text(changed_leaves.split('/-- The actual start of', 1)[0] + '\nend Zlib.Trees.Proofs\n')
            checked = build(scratch)
            if checked.returncode:
                raise RuntimeError('synchronized complete source equality failed:\n' + checked.stdout)
            print('KILLED ' + label + ': ' + first.group(1) + '; build_tree_eq_leaves still checks', flush=True)


if __name__ == '__main__':
    main()
