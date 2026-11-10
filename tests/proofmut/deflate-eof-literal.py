#!/usr/bin/env python3
"""The actual slow EOF prefix must settle the last deferred byte once."""
from pathlib import Path
import os
import re
import shutil
import subprocess
import tempfile


def main():
    root = Path(__file__).resolve().parents[2]
    lake = shutil.which('lake') or str(Path.home() / '.elan/bin/lake')
    source = Path('ZlibF/Zlib/deflate_strategies.c.lean')
    fragment = Path('ZlibF/Proof/deflate.c.engine.eof-insert.lean')
    proof = Path('ZlibF/Proof/deflate.c.engine.eof-literal.lean')
    originals = {p: (root / p).read_text() for p in (source, fragment, proof)}
    cases = (
        ('dropped-last-literal', 'let _ ← tally_lit s c', 'let _ := false'),
        ('retained-deferred-credit', 'wr s (fun d => { d with match_available := 0 })',
         'wr s (fun d => { d with match_available := 1 })'),
        ('wrong-final-byte', 'index8 d.window (d.strstart - 1).toNat', 'index8 d.window d.strstart.toNat'),
    )
    target = 'ZlibF.Proof.«deflate.c.engine.eof-tail»'
    env = dict(os.environ, LC_ALL='C')
    with tempfile.TemporaryDirectory(prefix='deflate-eof-literal-') as directory:
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

        require(build(target), 'positive complete actual EOF finish tail')
        print('baseline: complete actual EOF settlement, insert reset and final publication check', flush=True)
        for label, old, new in cases:
            left, rest = originals[source].split('def deflate_slow (', 1)
            body, right = rest.split('/-! ## `deflate_rle` -/', 1)
            if body.count(old) != 1 or originals[fragment].count(old) != 1:
                raise RuntimeError('ambiguous synchronized EOF literal mutation')
            (scratch / source).write_text(left + 'def deflate_slow (' + body.replace(old, new)
                                          + '/-! ## `deflate_rle` -/' + right)
            (scratch / fragment).write_text(originals[fragment].replace(old, new))
            require(build('ZlibF.Proof.«deflate.c.engine.eof-insert»'),
                    label + ' complete actual slow-function source equality')
            result = build(target)
            first = re.search(r'^error: ([^\n]+)', result.stdout, re.MULTILINE)
            hit = re.match(re.escape(str(proof)) + r':(\d+):', first.group(1)) if first else None
            text = originals[proof]
            start = text[:text.index('theorem slow_eof_literal_content_frame')].count('\n') + 1
            end = text[:text.index('theorem slow_eof_literal_content {')].count('\n') + 1
            resource = any(word in result.stdout.lower() for word in
                           ('maximum recursion depth', 'maximum number of heartbeats',
                            'deep recursion detected', 'deterministic timeout', 'interrupted', 'out of memory'))
            if result.returncode == 0 or hit is None or not start <= int(hit.group(1)) < end or resource:
                raise RuntimeError(label + ' survived or failed inconclusively:\n' + result.stdout)
            print('KILLED ' + label + ': ' + first.group(1)
                  + '; complete actual slow source equality checks; no resource failure', flush=True)


if __name__ == '__main__':
    main()
