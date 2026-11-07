#!/usr/bin/env python3
"""Actual BLOCK dispatch rejects extra marker writes after synchronized source gates."""
from pathlib import Path
import os
import re
import shutil
import subprocess
import tempfile


def main():
    root = Path(__file__).resolve().parents[2]
    lake = shutil.which('lake') or str(Path.home() / '.elan/bin/lake')
    source = Path('ZlibF/Zlib/deflate.c.lean')
    cut = Path('ZlibF/Proof/deflate.c.engine.public-source.lean')
    suffix = Path('ZlibF/Proof/deflate.c.engine.public-strategy-source.lean')
    originals = {p: (root / p).read_text() for p in (source, cut, suffix)}
    cases = (
        ('block-stored-marker', 'else if flush != Z_BLOCK then', 'else if flush == Z_BLOCK then'),
        ('block-align-marker', 'if flush == Z_PARTIAL_FLUSH then', 'if flush == Z_BLOCK then'),
    )
    proof = Path('ZlibF/Proof/deflate.c.engine.public-positive-source.lean')
    text = (root / proof).read_text()
    spans = []
    for theorem in ('public_strategy_block_done_ready',):
        marker = text.index('theorem ' + theorem)
        end = text.find('\ntheorem ', marker + 1)
        spans.append((text[:marker].count('\n') + 1,
                      len(text.splitlines()) + 1 if end < 0 else text[:end].count('\n') + 1))
    env = dict(os.environ, LC_ALL='C')
    caller = os.environ.get('ZLIBF_PUBLIC_FINISH_CALLER', 'deflate.c.engine.public-slow-block')
    target = 'ZlibF.Proof.«' + caller + '»'
    with tempfile.TemporaryDirectory(prefix='deflate-public-block-') as directory:
        scratch = Path(directory)
        for name in ('lakefile.toml', 'lean-toolchain'):
            shutil.copy2(root / name, scratch / name)
        shutil.copytree(root / 'ZlibF', scratch / 'ZlibF')
        shutil.copytree(root / '.lake/build', scratch / '.lake/build')

        def build(*targets):
            return subprocess.run([lake, 'build', *targets], cwd=scratch, env=env, text=True,
                                  stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=600)

        def require(result, label):
            if result.returncode:
                raise RuntimeError(label + ':\n' + result.stdout)

        require(build(target), 'positive actual default BLOCK data path')
        print('baseline: complete actual BLOCK strategy and public return check', flush=True)
        for label, old, new in cases:
            for p, indent in ((source, 4), (cut, 4), (suffix, 2)):
                old_text = ' ' * indent + old.replace('\n', '\n' + ' ' * indent)
                new_text = ' ' * indent + new.replace('\n', '\n' + ' ' * indent)
                # Comments can quote the same guard without being executable.
                if originals[p].count(old_text) != 1:
                    raise RuntimeError('ambiguous synchronized mutation: ' + str(p))
                (scratch / p).write_text(originals[p].replace(old_text, new_text))
            # Standalone source gate imports no public execution theorem.
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
            (scratch / 'ZlibF/Proof/deflate.c.engine.public-finish-source-gate.lean').write_text(
                gate + trailer + tail + actual + '\nend Zlib.Deflate.Engine.Proofs\n')
            require(build('ZlibF.Proof.«deflate.c.engine.public-finish-source-gate»'),
                    label + ' actual public function compilation and source equality gates')
            result = build(target)
            error = re.search(r'^error: ([^\n]+)', result.stdout, re.MULTILINE)
            hit = re.match(r'([^:]+):(\d+):', error.group(1)) if error else None
            expected = hit and hit.group(1) == str(proof) and any(
                start <= int(hit.group(2)) < end for start, end in spans)
            resource = any(word in result.stdout.lower() for word in
                           ('maximum recursion depth', 'maximum number of heartbeats',
                            'deep recursion detected', 'deterministic timeout', 'interrupted', 'out of memory'))
            if result.returncode == 0 or not expected or resource:
                raise RuntimeError(label + ' survived or failed inconclusively:\n' + result.stdout)
            print('KILLED ' + label + ': ' + error.group(1)
                  + '; complete public source and dispatch equalities check; no resource failure', flush=True)


if __name__ == '__main__':
    main()
