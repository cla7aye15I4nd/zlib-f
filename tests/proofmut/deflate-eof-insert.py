#!/usr/bin/env python3
"""The actual slow EOF write must retain exactly its two pending keys."""
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
    proof = Path('ZlibF/Proof/deflate.c.engine.eof-insert.lean')
    originals = {p: (root / p).read_text() for p in (source, proof)}
    old = 'if d.strstart < MIN_MATCH_u - 1 then d.strstart else MIN_MATCH_u - 1'
    cases = (('retain-three-positions', 'if d.strstart < MIN_MATCH_u then d.strstart else MIN_MATCH_u'),
             ('forget-pending-positions', 'if d.strstart < 0 then d.strstart else 0'))
    target = 'ZlibF.Proof.«deflate.c.engine.eof-insert»'
    env = dict(os.environ, LC_ALL='C')
    with tempfile.TemporaryDirectory(prefix='deflate-eof-insert-') as directory:
        scratch = Path(directory)
        for name in ('lakefile.toml', 'lean-toolchain'):
            shutil.copy2(root / name, scratch / name)
        shutil.copytree(root / 'ZlibF', scratch / 'ZlibF')
        shutil.copytree(root / '.lake/build', scratch / '.lake/build')

        def build():
            return subprocess.run([lake, 'build', target], cwd=scratch, env=env, text=True,
                                  stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=600)

        def require(result, label):
            if result.returncode:
                raise RuntimeError(label + ':\n' + result.stdout)

        require(build(), 'positive actual EOF write and content boundary')
        print('baseline: actual slow source equality, EOF write and restored content boundary check', flush=True)
        for label, new in cases:
            left, rest = originals[source].split('def deflate_slow (', 1)
            body, right = rest.split('/-! ## `deflate_rle` -/', 1)
            if body.count(old) != 1 or originals[proof].count(old) != 1:
                raise RuntimeError('ambiguous synchronized EOF write mutation')
            (scratch / source).write_text(left + 'def deflate_slow (' + body.replace(old, new)
                                          + '/-! ## `deflate_rle` -/' + right)
            text = originals[proof].replace(old, new)
            gate = text.split('theorem eof_insert_count', 1)[0]
            (scratch / proof).write_text(gate + '\nend Zlib.Deflate.Engine.Proofs\n')
            require(build(), label + ' complete actual slow-function source equality')
            (scratch / proof).write_text(text)
            result = build()
            first = re.search(r'^error: ([^\n]+)', result.stdout, re.MULTILINE)
            hit = re.match(re.escape(str(proof)) + r':(\d+):', first.group(1)) if first else None
            start = text[:text.index('theorem eof_insert_count')].count('\n') + 1
            end = text[:text.index('theorem eof_insert_content_boundary')].count('\n') + 1
            resource = any(word in result.stdout.lower() for word in
                           ('maximum recursion depth', 'maximum number of heartbeats',
                            'deep recursion detected', 'deterministic timeout', 'interrupted', 'out of memory'))
            if result.returncode == 0 or hit is None or not start <= int(hit.group(1)) < end or resource:
                raise RuntimeError(label + ' survived or failed inconclusively:\n' + result.stdout)
            print('KILLED ' + label + ': ' + first.group(1)
                  + '; complete actual slow source equality checks; no resource failure', flush=True)


if __name__ == '__main__':
    main()
