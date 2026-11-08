#!/usr/bin/env python3
"""Actual PARTIAL/SYNC markers and zero-length stored output reject mutants."""
from pathlib import Path
import os
import re
import shutil
import subprocess
import tempfile


def main():
    root = Path(__file__).resolve().parents[2]
    lake = shutil.which('lake') or str(Path.home() / '.elan/bin/lake')
    public = Path('ZlibF/Zlib/deflate.c.lean')
    cut = Path('ZlibF/Proof/deflate.c.engine.public-source.lean')
    suffix = Path('ZlibF/Proof/deflate.c.engine.public-strategy-source.lean')
    trees = Path('ZlibF/Zlib/trees.c.lean')
    header = Path('ZlibF/Proof/trees.c.stored-header.lean')
    copy = Path('ZlibF/Proof/trees.c.stored-copy.lean')
    paths = (public, cut, suffix, trees, header, copy)
    originals = {p: (root / p).read_text() for p in paths}
    env = dict(os.environ, LC_ALL='C')
    target = 'ZlibF.Proof.«deflate.c.engine.public-slow-partial-sync»'
    proof = Path('ZlibF/Proof/deflate.c.engine.partial-sync-return.lean')
    empty = Path('ZlibF/Proof/trees.c.empty-stored-marker.lean')

    def span(path, theorem):
        text = (root / path).read_text()
        start = text.index('theorem ' + theorem)
        end = text.find('\ntheorem ', start + 1)
        return (text[:start].count('\n') + 1,
                len(text.splitlines()) + 1 if end < 0 else text[:end].count('\n') + 1)

    def replace_once(text, old, new):
        if text.count(old) != 1:
            raise RuntimeError('ambiguous source mutation: ' + old)
        return text.replace(old, new)

    with tempfile.TemporaryDirectory(prefix='deflate-partial-sync-') as directory:
        scratch = Path(directory)
        for name in ('lakefile.toml', 'lean-toolchain'):
            shutil.copy2(root / name, scratch / name)
        shutil.copytree(root / 'ZlibF', scratch / 'ZlibF')
        shutil.copytree(root / '.lake/build', scratch / '.lake/build')

        def build(module):
            return subprocess.run([lake, 'build', module], cwd=scratch, env=env, text=True,
                                  stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=600)

        def require(result, label):
            if result.returncode:
                raise RuntimeError(label + ':\n' + result.stdout)

        def reject(result, label, path, theorem):
            error = re.search(r'^error: ([^\n]+)', result.stdout, re.MULTILINE)
            hit = re.match(re.escape(str(path)) + r':(\d+):', error.group(1)) if error else None
            start, end = span(path, theorem)
            resource = any(term in result.stdout.lower() for term in (
                'maximum recursion depth', 'maximum number of heartbeats', 'deep recursion detected',
                'deterministic timeout', 'interrupted', 'out of memory'))
            if result.returncode == 0 or not hit or not start <= int(hit.group(1)) < end or resource:
                raise RuntimeError(label + ' survived or failed inconclusively:\n' + result.stdout)
            print('KILLED ' + label + ': ' + error.group(1)
                  + '; actual source and synchronized source gates check; no resource failure', flush=True)

        require(build(target), 'positive complete actual PARTIAL/SYNC data paths')
        print('baseline: complete actual PARTIAL/SYNC data paths check', flush=True)
        cases = (
            ('sync-final-bit', '_tr_stored_block s (Ptr.null : BPtr) 0 0',
             '_tr_stored_block s (Ptr.null : BPtr) 0 1'),
            ('partial-stored-marker', '_tr_align s', '_tr_stored_block s (Ptr.null : BPtr) 0 0'),
        )
        for label, old, new in cases:
            for path in paths:
                (scratch / path).write_text(originals[path])
            for path, indent in ((public, 6), (cut, 6), (suffix, 4)):
                (scratch / path).write_text(replace_once(originals[path], ' ' * indent + old,
                                                       ' ' * indent + new))
            trailer = (root / 'ZlibF/Proof/deflate.c.engine.trailer-state.lean').read_text()
            trailer = trailer[trailer.index('def zlibTrailer ('):trailer.index('def zlibTrailerBuffer')]
            tail = (root / 'ZlibF/Proof/deflate.c.engine.trailer-output.lean').read_text()
            tail = tail[tail.index('def publicFinishTail'):tail.index('/-- The actual post-header')]
            actual = (scratch / suffix).read_text()
            actual = actual[actual.index('def publicStrategyReturn'):actual.index('\nend Zlib.Deflate.Engine.Proofs')]
            gate = ('import ZlibF.Proof.«deflate.c.engine.public-source»\n'
                    'namespace Zlib.Deflate.Engine.Proofs\n'
                    'open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public\n'
                    'open Zlib.Trees («_tr_stored_block» «_tr_align»)\nset_option autoImplicit false\n')
            (scratch / 'ZlibF/Proof/deflate.c.engine.partial-sync-source-gate.lean').write_text(
                gate + trailer + tail + actual + '\nend Zlib.Deflate.Engine.Proofs\n')
            require(build('ZlibF.Proof.«deflate.c.engine.partial-sync-source-gate»'), label + ' actual public source gates')
            reject(build(target), label, proof, 'public_strategy_partial_sync_source')

        for path in paths:
            (scratch / path).write_text(originals[path])
        left, body = originals[trees].split('def «_tr_stored_block»', 1)
        middle, right = body.split('/-- `void ZLIB_INTERNAL _tr_flush_bits', 1)
        middle = replace_once(middle, 'pending := d.pending + stored_len',
                              'pending := d.pending + stored_len + 1')
        (scratch / trees).write_text(left + 'def «_tr_stored_block»' + middle
                                    + '/-- `void ZLIB_INTERNAL _tr_flush_bits' + right)
        for path in (header, copy):
            changed = replace_once(originals[path], 'pending := d.pending + length',
                                   'pending := d.pending + length + 1')
            if path == copy:
                # Keep both exact source fragments/equalities, omit unrelated
                # nonzero copy proofs so the zero-length execution must reject it.
                changed = changed.split('/-- The actual copy reads', 1)[0]
                changed += '\nend Zlib.Trees.Proofs.Out\n'
            (scratch / path).write_text(changed)
        require(build('ZlibF.Proof.«trees.c.stored-copy»'), 'zero-count actual stored source gates')
        reject(build('ZlibF.Proof.«trees.c.empty-stored-marker»'), 'zero-count-off-by-one', empty,
               'stored_zero_null_emit')


if __name__ == '__main__':
    main()
