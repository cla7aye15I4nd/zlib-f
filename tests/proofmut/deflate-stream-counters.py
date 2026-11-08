#!/usr/bin/env python3
"""Reject real read_buf and flush_pending total-counter mutations.

The complete ordinary strategy counter theorem is the positive caller.
Every mutated translation must compile, then fail in the matching function's
execution proof. Resource failures are inconclusive. Production files are
never changed.
"""
from pathlib import Path
import os
import re
import shutil
import subprocess
import tempfile


def main():
    root = Path(__file__).resolve().parents[2]
    lake = shutil.which('lake') or str(Path.home() / '.elan/bin/lake')
    source = Path('ZlibF/Zlib/deflate_base.c.lean')
    original = (root / source).read_text()
    read_proof = Path('ZlibF/Proof/deflate.c.engine.readbuf.lean')
    read_original = (root / read_proof).read_text()
    cases = (
        ('input-total-drop', 'total_in := z.total_in + len.toUInt64',
         'total_in := z.total_in', 'readbuf', 'read_buf_ok'),
        ('input-total-off-by-one', 'total_in := z.total_in + len.toUInt64',
         'total_in := z.total_in + len.toUInt64 + 1', 'readbuf', 'read_buf_ok'),
        ('output-total-drop', 'total_out := z.total_out + len.toUInt64',
         'total_out := z.total_out', 'pending-output', 'flush_pending_low_raw'),
        ('output-total-off-by-one', 'total_out := z.total_out + len.toUInt64',
         'total_out := z.total_out + len.toUInt64 + 1', 'pending-output', 'flush_pending_low_raw'),
    )
    spans = {}
    for _, _, _, name, theorem in cases:
        path = Path('ZlibF/Proof/deflate.c.engine.' + name + '.lean')
        text = (root / path).read_text()
        marker = text.index('theorem ' + theorem)
        following = text.find('\ntheorem ', marker + 1)
        spans[(name, theorem)] = (str(path), text[:marker].count('\n') + 1,
                                  len(text.splitlines()) + 1 if following < 0 else text[:following].count('\n') + 1)
    with tempfile.TemporaryDirectory(prefix='deflate-stream-counters-') as directory:
        scratch = Path(directory)
        for name in ('lakefile.toml', 'lean-toolchain'):
            shutil.copy2(root / name, scratch / name)
        shutil.copytree(root / 'ZlibF', scratch / 'ZlibF')
        shutil.copytree(root / '.lake/build', scratch / '.lake/build')

        def build(module):
            return subprocess.run([lake, 'build', module], cwd=scratch,
                                  env=dict(os.environ, LC_ALL='C'), text=True,
                                  stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=600)

        baseline = build('ZlibF.Proof.«deflate.c.engine.ordinary-call-counters»')
        if baseline.returncode:
            raise RuntimeError('positive complete ordinary strategy counters:\n' + baseline.stdout)
        print('baseline: complete real NO_FLUSH and FINISH strategy counter proofs check', flush=True)
        for label, old, new, name, theorem in cases:
            if original.count(old) != 1:
                raise RuntimeError('ambiguous actual-source mutation: ' + label)
            (scratch / source).write_text(original.replace(old, new))
            # Keep the source-extraction record update faithful to the mutated
            # read_buf. The unchanged actual-copy result must detect the error.
            # This avoids counting a large source-definitional-equality timeout.
            synchronized = read_original
            if name == 'readbuf':
                before, after = read_original.split('/-- `read_buf` with the length already computed', 1)
                helper_old = old.replace('len.toUInt64', 'L.toUInt64')
                helper_new = new.replace('len.toUInt64', 'L.toUInt64')
                if before.count(helper_old) != 1:
                    raise RuntimeError('ambiguous read source helper: ' + label)
                synchronized = before.replace(helper_old, helper_new) + '/-- `read_buf` with the length already computed' + after
            (scratch / read_proof).write_text(synchronized)
            compiled = build('ZlibF.Zlib.«deflate_base.c»')
            if compiled.returncode:
                raise RuntimeError(label + ' source compilation:\n' + compiled.stdout)
            result = build('ZlibF.Proof.«deflate.c.engine.' + name + '»')
            error = re.search(r'^error: ([^\n]+)', result.stdout, re.MULTILINE)
            path, start, end = spans[(name, theorem)]
            hit = re.match(re.escape(path) + r':(\d+):', error.group(1)) if error else None
            resource = any(word in result.stdout.lower() for word in (
                'maximum recursion depth', 'maximum number of heartbeats', 'deep recursion detected',
                'deterministic timeout', 'interrupted', 'out of memory'))
            if result.returncode == 0 or hit is None or resource or not start <= int(hit.group(1)) < end:
                raise RuntimeError(label + ' survived or failed inconclusively:\n' + result.stdout)
            print('KILLED ' + label + ': ' + error.group(1)
                  + '; actual source compiles; no resource failure', flush=True)


if __name__ == '__main__':
    main()
