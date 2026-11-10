#!/usr/bin/env python3
"""Reject actual main-loop entry bugs with the complete default run in scope.

Only in the scratch baseline, omit older restricted raw-copy end-to-end
examples that would reject the same source edits earlier. No assumptions
replace them, and the original checkout is unchanged.
"""
from pathlib import Path
import os
import re
import shutil
import subprocess
import tempfile


def main():
    root = Path(__file__).resolve().parents[2]
    source = Path('ZlibF/Zlib/inflate.c.lean')
    proof = Path('ZlibF/Proof/inflate.c.dispatch-entry.lean')
    original = (root / source).read_text()
    checked = (root / proof).read_text()
    variants = (
        ('wrong-type-normalization', 'then setMode c.st TYPEDO', 'then setMode c.st LEN_'),
        ('omitted-load', 'LOAD c.strm c.st', 'modify fun l => l'),
        ('wrong-input-base', 'in_ := l.have_', 'in_ := 0'),
        ('false-loop-condition', 'xwhile (pure true) (inflate_dispatch c)',
         'xwhile (pure false) (inflate_dispatch c)'),
        ('omitted-mode-loop', 'xwhile (pure true) (inflate_dispatch c)', 'modify fun l => l'),
    )
    env = os.environ.copy()
    env['LC_ALL'] = 'C'
    target = 'ZlibF.Proof.«inflate.c.default-run»'

    def build(where):
        return subprocess.run(['lake', 'build', target], cwd=where, env=env, text=True,
                              stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=600)

    with tempfile.TemporaryDirectory(prefix='inflate-default-run-') as directory:
        scratch = Path(directory)
        for name in ('lakefile.toml', 'lean-toolchain'):
            shutil.copy2(root / name, scratch / name)
        shutil.copytree(root / 'ZlibF', scratch / 'ZlibF')
        shutil.copytree(root / '.lake', scratch / '.lake', ignore=shutil.ignore_patterns('*.tmp.*', 'Index.*'))
        stored = scratch / 'ZlibF/Proof/inflate.c.stored-call.lean'
        text = stored.read_text()
        a = text.rindex('/--', 0, text.index('theorem inflate_leave_raw_finish_done'))
        b = text.rindex('/--', 0, text.index('theorem LOAD_run'))
        c = text.rindex('/--', 0, text.index('theorem inflate_run_raw_copy'))
        stored.write_text(text[:a] + text[b:c] + '\nend Zlib.Inflate.Proofs\n')
        baseline = build(scratch)
        if baseline.returncode:
            raise RuntimeError('baseline failed:\n' + baseline.stdout)
        print('baseline: complete actual default inflate_run and bounded loop check', flush=True)
        for label, old, new in variants:
            a = original.index('def inflate_run (')
            b = original.index('def inflate_leave (', a)
            section = original[a:b]
            if section.count(old) != 1:
                raise RuntimeError('ambiguous actual main-loop edit: ' + label)
            (scratch / source).write_text(original[:a] + section.replace(old, new) + original[b:])
            result = build(scratch)
            first = re.search(r'^error: ([^\n]+)', result.stdout, re.MULTILINE)
            hit = re.match(re.escape(str(proof)) + r':(\d+):', first.group(1)) if first else None
            a = checked.index('theorem inflate_run_output_entry_frame_state ')
            b = checked.index('/-- Projection retaining', a)
            low = checked[:a].count('\n') + 1
            high = checked[:b].count('\n') + 1
            exhausted = any(term in result.stdout.lower() for term in (
                'maximum recursion depth', 'maximum number of heartbeats', 'deterministic timeout'))
            if result.returncode == 0 or hit is None or not low <= int(hit.group(1)) <= high or exhausted:
                raise RuntimeError(label + ' lacks a direct non-resource proof failure:\n' + result.stdout)
            print('KILLED ' + label + ': ' + first.group(1), flush=True)
        print('PASS: five actual inflate_run mutants; no resource failures', flush=True)


if __name__ == '__main__':
    main()
