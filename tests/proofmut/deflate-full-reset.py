#!/usr/bin/env python3
"""Actual FULL marker, hash clear and position reset reject source mutants."""
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
    public = Path('ZlibF/Zlib/deflate.c.lean')
    cut = Path('ZlibF/Proof/deflate.c.engine.public-source.lean')
    suffix = Path('ZlibF/Proof/deflate.c.engine.public-strategy-source.lean')
    paths = (public, cut, suffix)
    originals = {p: (root / p).read_text() for p in paths}
    env = dict(os.environ, LC_ALL='C')
    target = 'ZlibF.Proof.«deflate.c.engine.public-slow-full»'
    selection = set(sys.argv[1:])
    labels = {'full-final-bit', 'full-history-not-cleared', 'full-position-off-by-one'}
    if selection - labels:
        raise RuntimeError('unknown mutation labels: ' + ', '.join(sorted(selection - labels)))
    proof = Path('ZlibF/Proof/deflate.c.engine.full-flush-return.lean')

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

    with tempfile.TemporaryDirectory(prefix='deflate-full-reset-') as directory:
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

        require(build(target), 'positive complete actual FULL data path')
        print('baseline: complete actual FULL data path checks', flush=True)
        cases = (
            ('full-final-bit', '_tr_stored_block s (Ptr.null : BPtr) 0 0',
             '_tr_stored_block s (Ptr.null : BPtr) 0 1'),
            ('full-history-not-cleared', 'CLEAR_HASH s                                        -- forget history',
             'pure ()                                        -- forget history'),
            ('full-position-off-by-one',
             'wr s (fun d => { d with strstart := 0, block_start := 0, insert := 0 })',
             'wr s (fun d => { d with strstart := 1, block_start := 0, insert := 0 })'),
        )
        for label, old, new in cases:
            if selection and label not in selection:
                continue
            for path in paths:
                (scratch / path).write_text(originals[path])
            for path, indent in ((public, 6), (cut, 6), (suffix, 4)):
                text = originals[path]
                if path == public:
                    before, body = text.split('def deflate (strm : ZStreamPtr)', 1)
                    body, after = body.split('/-- `int ZEXPORT deflateParams(', 1)
                    body = replace_once(body, ' ' * indent + old, ' ' * indent + new)
                    text = before + 'def deflate (strm : ZStreamPtr)' + body
                    text += '/-- `int ZEXPORT deflateParams(' + after
                else:
                    text = replace_once(text, ' ' * indent + old, ' ' * indent + new)
                (scratch / path).write_text(text)
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
            (scratch / 'ZlibF/Proof/deflate.c.engine.full-reset-source-gate.lean').write_text(
                gate + trailer + tail + actual + '\nend Zlib.Deflate.Engine.Proofs\n')
            require(build('ZlibF.Proof.«deflate.c.engine.full-reset-source-gate»'), label + ' actual public source gates')
            reject(build(target), label, proof, 'public_strategy_full_source')



if __name__ == '__main__':
    main()
