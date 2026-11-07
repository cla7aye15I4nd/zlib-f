#!/usr/bin/env python3
"""Actual longest_match must clip its result to valid lookahead at EOF."""
from pathlib import Path
import os
import re
import shutil
import subprocess
import tempfile


def main():
    root = Path(__file__).resolve().parents[2]
    source = Path('ZlibF/Zlib/deflate_strategies.c.lean')
    proof = Path('ZlibF/Proof/deflate.c.engine.lmmain.lean')
    originals = {p: (root / p).read_text() for p in (source, proof)}
    variants = (
        ('reversed-lookahead-clamp',
         'if st.best_len.toUInt32 ≤ lookahead then return st.best_len.toUInt32',
         'if st.best_len.toUInt32 ≥ lookahead then return st.best_len.toUInt32'),
        ('clipped-length-plus-one', '  return lookahead', '  return (lookahead + 1)'),
    )
    env = dict(os.environ, LC_ALL='C')
    lake = shutil.which('lake') or str(Path.home() / '.elan/bin/lake')

    def build(where, *targets):
        return subprocess.run([lake, 'build', *targets], cwd=where, env=env, text=True,
                              stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=600)

    def success(result, label):
        if result.returncode:
            raise RuntimeError(label + ':\n' + result.stdout)

    with tempfile.TemporaryDirectory(prefix='deflate-match-clipping-') as directory:
        scratch = Path(directory)
        for name in ('lakefile.toml', 'lean-toolchain'):
            shutil.copy2(root / name, scratch / name)
        shutil.copytree(root / 'ZlibF', scratch / 'ZlibF')
        shutil.copytree(root / '.lake/build', scratch / '.lake/build')
        success(build(scratch, 'ZlibF.Proof.«deflate.c.engine.finish-search»',
                      'ZlibF.Proof.«deflate.c.engine.fill-comparison-room»'), 'positive short search and physical-room caller')
        print('baseline: every search length, clipped matches and real refill comparison room check', flush=True)
        for label, old, new in variants:
            left, body = originals[source].split('def longest_match (', 1)
            middle, right = body.split('/-! ## Loop state of the compression functions -/', 1)
            if middle.count(old) != 1 or originals[proof].count(old) != 2:
                raise RuntimeError('ambiguous actual/named clipping mutation')
            (scratch / source).write_text(left + 'def longest_match (' + middle.replace(old, new)
                                         + '/-! ## Loop state of the compression functions -/' + right)
            text = originals[proof].replace(old, new)
            # Keep the complete actual-function source equality and named tail,
            # without asking its unchanged execution specification to pass.
            gate = text.split('theorem lmRest_ok', 1)[0]
            (scratch / proof).write_text(gate + '\nend Zlib.Deflate.Engine.Proofs\n')
            success(build(scratch, 'ZlibF.Proof.«deflate.c.engine.lmmain»'), label + ' complete actual-function source equality')
            (scratch / proof).write_text(text)
            result = build(scratch, 'ZlibF.Proof.«deflate.c.engine.lmmain»')
            first = re.search(r'^error: ([^\n]+)', result.stdout, re.MULTILINE)
            hit = re.match(re.escape(str(proof)) + r':(\d+):', first.group(1)) if first else None
            start = text[:text.index('theorem lmRest_ok')].count('\n') + 1
            end = text[:text.index('theorem longest_match_ok')].count('\n') + 1
            resource = any(word in result.stdout.lower() for word in
                           ('maximum recursion depth', 'maximum number of heartbeats', 'deep recursion detected',
                            'deterministic timeout', 'interrupted', 'out of memory'))
            if result.returncode == 0 or hit is None or not start <= int(hit.group(1)) < end or resource:
                raise RuntimeError(label + ' survived or failed outside longest_match clipping execution:\n' + result.stdout)
            print('KILLED ' + label + ': ' + first.group(1)
                  + '; complete source equality checks; no resource failure', flush=True)


if __name__ == '__main__':
    main()
