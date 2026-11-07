#!/usr/bin/env python3
"""Reject actual preparation/selection regressions in their execution proofs.

Both complete source equalities must check after synchronizing their named
fragments. Computed costs appear as explicit branch conditions. No callee contract is
assumed by the complete fixed-path result. Resource failures are inconclusive.
"""
from pathlib import Path
import os
import re
import shutil
import subprocess
import sys
import tempfile


def main():
    root = Path(__file__).resolve().parents[2]
    lake = shutil.which('lake') or str(Path.home() / '.elan/bin/lake')
    source = Path('ZlibF/Zlib/trees.c.lean')
    cut = Path('ZlibF/Proof/trees.c.flush-source.lean')
    prepare = Path('ZlibF/Proof/deflate.c.engine.block-prepare.lean')
    originals = {p: (root / p).read_text() for p in (source, cut, prepare)}
    cases = (
        ('inflated-static-cost', 'cost', 'static_lenb := ((← rd s).static_len + 3 + 7) >>> 3',
         'static_lenb := ((← rd s).static_len + 3 + 7) >>> 2', 'flush-fixed', 'flush_fixed_dispatch'),
        ('reversed-static-preference', 'cost', 'if static_lenb ≤ opt_lenb ∨', 'if static_lenb ≥ opt_lenb ∨',
         'flush-fixed', 'flush_fixed_dispatch'),
        ('wrong-stored-threshold', 'cost', 'if stored_len + 4 ≤ opt_lenb ∧ buf != .null then',
         'if stored_len + 3 ≤ opt_lenb ∧ buf != .null then', 'flush-fixed', 'flush_fixed_dispatch'),
        ('reversed-fixed-selection', 'cost', 'else if static_lenb == opt_lenb then',
         'else if static_lenb != opt_lenb then', 'flush-fixed', 'flush_fixed_dispatch'),
        ('discard-detected-hint', 'hint', 'data_type := t }', 'data_type := Z_UNKNOWN }',
         'block-prepare', 'block_data_type_engine'),
    )
    selected = set(sys.argv[1:])
    if selected:
        unknown = selected - {x[0] for x in cases}
        if unknown:
            raise RuntimeError('unknown mutation labels: ' + ', '.join(sorted(unknown)))
        cases = tuple(x for x in cases if x[0] in selected)

    def replace_scoped(text, first, last, old, new, label):
        before, body = text.split(first, 1)
        body, after = body.split(last, 1)
        if body.count(old) != 1:
            raise RuntimeError('ambiguous source mutation: ' + label)
        return before + first + body.replace(old, new) + last + after

    with tempfile.TemporaryDirectory(prefix='deflate-flush-fixed-') as directory:
        scratch = Path(directory)
        for name in ('lakefile.toml', 'lean-toolchain'):
            shutil.copy2(root / name, scratch / name)
        shutil.copytree(root / 'ZlibF', scratch / 'ZlibF')
        shutil.copytree(root / '.lake/build', scratch / '.lake/build')

        def build(module):
            return subprocess.run([lake, 'build', module], cwd=scratch,
                                  env=dict(os.environ, LC_ALL='C'), text=True,
                                  stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=600)

        def require(result, label):
            if result.returncode:
                raise RuntimeError(label + ':\n' + result.stdout)

        target = 'ZlibF.Proof.«deflate.c.engine.flush-fixed»'
        require(build(target), 'positive complete fixed-choice baseline')
        print('baseline: real hint, builders, costs, fixed branch and final/nonfinal tails', flush=True)
        for label, scope, old, new, module, theorem in cases:
            (scratch / source).write_text(replace_scoped(originals[source],
                'def «_tr_flush_block» (', '/-- `int ZLIB_INTERNAL _tr_tally', old, new, label))
            if originals[cut].count(old) != 1:
                raise RuntimeError('ambiguous first source cut: ' + label)
            (scratch / cut).write_text(originals[cut].replace(old, new))
            if scope == 'hint':
                changed = replace_scoped(originals[prepare], 'def blockDataType (',
                                         '/-- The exact three constructors', old, new, label)
            else:
                # The engine namespace needs the qualified record reader.
                qold = old.replace('rd s', 'Zlib.Trees.rd s')
                qnew = new.replace('rd s', 'Zlib.Trees.rd s')
                changed = replace_scoped(originals[prepare], 'section source', 'end source', qold, qnew, label)
            require(build('ZlibF.Zlib.«trees.c»'), label + ' actual source compilation')
            require(build('ZlibF.Proof.«trees.c.flush-source»'), label + ' complete first source equality')
            prefix = changed.split('/-- Updating only the public hint', 1)[0]
            equality = 'section source' + changed.split('section source', 1)[1]
            (scratch / prepare).write_text(prefix + equality)
            require(build('ZlibF.Proof.«deflate.c.engine.block-prepare»'), label + ' complete preparation source equality')
            (scratch / prepare).write_text(changed)
            p = Path('ZlibF/Proof/deflate.c.engine.' + module + '.lean')
            text = changed if p == prepare else (root / p).read_text()
            start_offset = text.index('theorem ' + theorem)
            following = text.find('\ntheorem ', start_offset + len('theorem ' + theorem))
            start = text[:start_offset].count('\n') + 1
            end = len(text.splitlines()) + 1 if following < 0 else text[:following].count('\n') + 1
            result = build(target)
            error = re.search(r'^error: ([^\n]+)', result.stdout, re.MULTILINE)
            hit = re.match(re.escape(str(p)) + r':(\d+):', error.group(1)) if error else None
            resource = any(word in result.stdout.lower() for word in (
                'maximum recursion depth', 'maximum number of heartbeats', 'deep recursion detected',
                'deterministic timeout', 'interrupted', 'out of memory'))
            if result.returncode == 0 or hit is None or resource or not start <= int(hit.group(1)) < end:
                raise RuntimeError(label + ' survived or failed inconclusively:\n' + result.stdout)
            print('KILLED ' + label + ': ' + error.group(1) + '; both complete source equalities check', flush=True)


if __name__ == '__main__':
    main()
