#!/usr/bin/env python3
"""Reject actual full/mid bit-publication and pending-copy regressions.

Source compilation precedes every rejection. Only errors in the affected
function's execution proof count. Resource failures are inconclusive.
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
    base = Path('ZlibF/Zlib/deflate_base.c.lean')
    trees = Path('ZlibF/Zlib/trees.c.lean')
    originals = {p: (root / p).read_text() for p in (base, trees)}
    cases = (
        ('skip-bit-publication', base, '_tr_flush_bits s', 'pure ()',
         'deflate.c.engine.output-state', 'flush_pending_prepare'),
        ('word-residual-count', trees, 'md s fun d => { d with bi_valid := 0 }',
         'md s fun d => { d with bi_valid := 8 }', 'trees.c.bits', 'bi_flush_16'),
        ('middle-byte-threshold', trees, 'else if d.bi_valid ≥ 8 then',
         'else if d.bi_valid > 8 then', 'trees.c.bits', 'bi_flush_mid'),
        ('middle-byte-shift', trees, 'md s fun d => { d with bi_buf := d.bi_buf >>> 8 }',
         'md s fun d => { d with bi_buf := d.bi_buf >>> 7 }', 'trees.c.bits', 'bi_flush_mid'),
        ('pending-cursor-reset', base, 'if pend == 0 then wr s',
         'if pend != 0 then wr s', 'deflate.c.engine.pending-output', 'flush_pending_low_raw'),
    )
    selection = set(sys.argv[1:])
    if selection:
        unknown = selection - {case[0] for case in cases}
        if unknown:
            raise RuntimeError('unknown mutation labels: ' + ', '.join(sorted(unknown)))
        cases = tuple(case for case in cases if case[0] in selection)
    spans = {}
    for _, _, _, _, proof, theorem in cases:
        path = 'ZlibF/Proof/' + proof + '.lean'
        text = (root / path).read_text()
        anchor = 'theorem ' + theorem
        start = text[:text.index(anchor)].count('\n') + 1
        following = text.find('\ntheorem ', text.index(anchor) + len(anchor))
        end = len(text.splitlines()) + 1 if following < 0 else text[:following].count('\n') + 1
        spans[(proof, theorem)] = (path, start, end)
    with tempfile.TemporaryDirectory(prefix='deflate-block-output-') as directory:
        scratch = Path(directory)
        for name in ('lakefile.toml', 'lean-toolchain'):
            shutil.copy2(root / name, scratch / name)
        shutil.copytree(root / 'ZlibF', scratch / 'ZlibF')
        shutil.copytree(root / '.lake/build', scratch / '.lake/build')

        def build(target):
            return subprocess.run([lake, 'build', target], cwd=scratch,
                                  env=dict(os.environ, LC_ALL='C'), text=True,
                                  stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=240)

        def require(result, label):
            if result.returncode:
                raise RuntimeError(label + ':\n' + result.stdout)

        module = 'ZlibF.Proof.«deflate.c.engine.pending-block-output»'
        require(build(module), 'positive complete pending-publication baseline')
        print('baseline: actual 0..16-bit publication, partial/zero/full copy, exact bit stream and allocation frame', flush=True)
        for label, path, old, new, proof, theorem in cases:
            for p, text in originals.items():
                (scratch / p).write_text(text)
            original = originals[path]
            first = 'def flush_pending (' if path == base else 'def bi_flush ('
            last = '/-- `FLUSH_BLOCK_ONLY(' if path == base else '/-- `local void bi_windup('
            before, rest = original.split(first, 1)
            middle, after = rest.split(last, 1)
            if middle.count(old) != 1:
                raise RuntimeError('ambiguous mutation: ' + label)
            (scratch / path).write_text(before + first + middle.replace(old, new) + last + after)
            target = 'ZlibF.Zlib.«deflate_base.c»' if path == base else 'ZlibF.Zlib.«trees.c»'
            require(build(target), label + ' source compilation')
            result = build(module)
            error = re.search(r'^error: ([^\n]+)', result.stdout, re.MULTILINE)
            expected, start, end = spans[(proof, theorem)]
            hit = re.match(re.escape(expected) + r':(\d+):', error.group(1)) if error else None
            resource = any(word in result.stdout.lower() for word in (
                'maximum recursion depth', 'maximum number of heartbeats', 'deep recursion detected',
                'deterministic timeout', 'interrupted', 'out of memory'))
            if result.returncode == 0 or hit is None or resource or not start <= int(hit.group(1)) < end:
                raise RuntimeError(label + ' survived or failed inconclusively:\n' + result.stdout)
            print('KILLED ' + label + ': ' + error.group(1), flush=True)


if __name__ == '__main__':
    main()
