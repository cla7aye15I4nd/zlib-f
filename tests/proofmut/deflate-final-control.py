#!/usr/bin/env python3
"""Reject actual final macro and finish-tail control mutations."""
from pathlib import Path
import os
import re
import shutil
import subprocess
import tempfile


def main():
    root = Path(__file__).resolve().parents[2]
    lake = shutil.which('lake') or str(Path.home() / '.elan/bin/lake')
    base = Path('ZlibF/Zlib/deflate_base.c.lean')
    strategies = Path('ZlibF/Zlib/deflate_strategies.c.lean')
    proof = Path('ZlibF/Proof/deflate.c.engine.final-control.lean')
    originals = {p: (root / p).read_text() for p in (base, strategies)}
    text = (root / proof).read_text()
    cases = (
        ('lost-wrapper-trailer-return', base, 'def FLUSH_BLOCK (', None,
         'if d.pending != 0 || d.wrap != 0 then return some finish_started',
         'if d.pending != 0 then return some finish_started', 'flush_final_loop_boundary'),
        ('wrong-final-macro-return', base, 'def FLUSH_BLOCK (', None,
         'return some finish_started', 'return some finish_done', 'flush_final_loop_boundary'),
        ('nonfinal-tail-block', strategies, 'def finish_tail (', '/-! ## `deflate_stored` -/',
         'FLUSH_BLOCK s 1', 'FLUSH_BLOCK s 0', 'finish_tail_final_boundary'),
        ('wrong-completed-tail-return', strategies, 'def finish_tail (', '/-! ## `deflate_stored` -/',
         'return finish_done', 'return block_done', 'finish_tail_final_boundary'),
    )
    env = dict(os.environ, LC_ALL='C')
    target = 'ZlibF.Proof.«deflate.c.engine.final-control»'
    with tempfile.TemporaryDirectory(prefix='deflate-final-control-') as directory:
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

        require(build(target), 'positive actual final macro and finish tail')
        print('baseline: final publication and actual finish-tail return check', flush=True)
        for label, source, marker, endmarker, old, new, theorem in cases:
            for path, contents in originals.items():
                (scratch / path).write_text(contents)
            left, rest = originals[source].split(marker, 1)
            body, right = rest.split(endmarker, 1) if endmarker else (rest, '')
            if body.count(old) != 1:
                raise RuntimeError('ambiguous final-control mutation: ' + label)
            (scratch / source).write_text(left + marker + body.replace(old, new)
                                          + ((endmarker + right) if endmarker else ''))
            require(build('ZlibF.Zlib.«' + source.stem + '»'), label + ' actual translated function compiles')
            result = build(target)
            first = re.search(r'^error: ([^\n]+)', result.stdout, re.MULTILINE)
            hit = re.match(re.escape(str(proof)) + r':(\d+):', first.group(1)) if first else None
            start = text[:text.index('theorem ' + theorem)].count('\n') + 1
            next_theorem = text.find('\ntheorem ', text.index('theorem ' + theorem) + 1)
            end = len(text.splitlines()) + 1 if next_theorem < 0 else text[:next_theorem].count('\n') + 1
            resource = any(word in result.stdout.lower() for word in
                           ('maximum recursion depth', 'maximum number of heartbeats',
                            'deep recursion detected', 'deterministic timeout', 'interrupted', 'out of memory'))
            if result.returncode == 0 or hit is None or not start <= int(hit.group(1)) < end or resource:
                raise RuntimeError(label + ' survived or failed inconclusively:\n' + result.stdout)
            print('KILLED ' + label + ': ' + first.group(1)
                  + '; actual translated function compiles; no resource failure', flush=True)


if __name__ == '__main__':
    main()
