#!/usr/bin/env python3
"""Reject actual read_buf checksum changes in its execution proof.

The complete translated function compiles first. A separate source gate
checks its whole-function equality to the synchronized length cutpoint.
Only a non-resource failure in read_buf_ok counts as rejection.
"""
from pathlib import Path
import os
import re
import shutil
import subprocess
import tempfile


def main():
    root = Path(__file__).resolve().parents[2]
    lake = shutil.which('lake')
    if lake is None:
        raise RuntimeError('lake is required')
    source = Path('ZlibF/Zlib/deflate_base.c.lean')
    proof = Path('ZlibF/Proof/deflate.c.engine.readbuf.lean')
    original = (root / source).read_text()
    cut = (root / proof).read_text()
    start = cut[:cut.index('theorem read_buf_ok ')].count('\n') + 1
    following = cut.find('\ntheorem ', cut.index('theorem read_buf_ok ') + 1)
    end = len(cut.splitlines()) + 1 if following < 0 else cut[:following].count('\n') + 1
    variants = (
        ('keep-old-checksum',
         'zwr strm (fun z => { z with adler := r })',
         'zwr strm (fun z => { z with adler := a })',
         'zwr strm (rbSetAd r)', 'zwr strm (rbSetAd a)'),
        ('reset-checksum-seed',
         'let r ← Zlib.Adler32.adler32 a buf len',
         'let r ← Zlib.Adler32.adler32 1 buf len',
         'let r ← Zlib.Adler32.adler32 a buf len',
         'let r ← Zlib.Adler32.adler32 1 buf len'),
        ('omit-final-checksum-byte',
         'let r ← Zlib.Adler32.adler32 a buf len',
         'let r ← Zlib.Adler32.adler32 a buf (len - 1)',
         'let r ← Zlib.Adler32.adler32 a buf len',
         'let r ← Zlib.Adler32.adler32 a buf (len - 1)'),
    )
    with tempfile.TemporaryDirectory(prefix='deflate-read-checksum-') as directory:
        scratch = Path(directory)
        for name in ('lakefile.toml', 'lean-toolchain'):
            shutil.copy2(root / name, scratch / name)
        shutil.copytree(root / 'ZlibF', scratch / 'ZlibF')
        shutil.copytree(root / '.lake/build', scratch / '.lake/build')

        def build(target):
            return subprocess.run([lake, 'build', target], cwd=scratch,
                                  env=dict(os.environ, LC_ALL='C'), text=True,
                                  stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=600)

        def require(result, label):
            if result.returncode:
                raise RuntimeError(label + ':\n' + result.stdout)

        require(build('ZlibF.Proof.«deflate.c.engine.body-checksum»'), 'positive actual checksum body')
        print('baseline: actual refill, all block choices and complete ordinary body checksums', flush=True)
        for label, old, new, old_cut, new_cut in variants:
            before, body = original.split('def read_buf (', 1)
            body, after = body.split('/-- `local void fill_window', 1)
            left, core = cut.split('def rbCore (', 1)
            core, right = core.split('\ntheorem read_buf_eq ', 1)
            # The two stores are the Adler and CRC branches. Only the
            # first is changed, and neither surrounding declaration moves.
            if old not in body or old_cut not in core:
                raise RuntimeError('missing mutation: ' + label)
            changed_core = core.replace(old_cut, new_cut, 1)
            (scratch / source).write_text(before + 'def read_buf (' + body.replace(old, new, 1)
                                         + '/-- `local void fill_window' + after)
            (scratch / proof).write_text(left + 'def rbCore (' + changed_core + '\ntheorem read_buf_eq ' + right)
            require(build('ZlibF.Zlib.«deflate_base.c»'), label + ' translated source')
            gate = scratch / '.lake/read-checksum-source.lean'
            gate.write_text(
                'import ZlibF.Proof.«deflate.c.engine.macros»\n'
                'namespace Zlib.Deflate.Engine.Proofs\nopen C Zlib.Deflate\n'
                'def rbLen (avail size : UInt32) : UInt32 := if avail > size then size else avail\n'
                'def rbDec (len : UInt32) : ZStream → ZStream := fun z => {z with avail_in := z.avail_in - len}\n'
                'def rbSetAd (a : UInt64) : ZStream → ZStream := fun z => {z with adler := a}\n'
                'def rbAdvF (ni : BPtr) (len : UInt32) : ZStream → ZStream := '
                'fun z => {z with next_in := ni, total_in := z.total_in + len.toUInt64}\n'
                'def rbCore (' + changed_core + '\n'
                'theorem source (h : Heap) (r : ZStreamRef) (z : ZStream) (buf : BPtr) (size : UInt32) '
                '(hz : r.get h = some z) : read_buf (some r) buf size h = '
                'rbCore (some r) buf (rbLen z.avail_in size) h := by\n'
                '  unfold read_buf rbCore rbLen\n'
                '  simp only [zrd_eq, hz, bind_app, pure_app]\n'
                '  by_cases big : z.avail_in > size <;> simp only [big, if_true, if_false]\n'
                '  all_goals rfl\nend Zlib.Deflate.Engine.Proofs\n')
            checked = subprocess.run([lake, 'env', 'lean', str(gate)], cwd=scratch,
                                     env=dict(os.environ, LC_ALL='C'), text=True,
                                     stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=600)
            require(checked, label + ' complete synchronized source equality')
            result = build('ZlibF.Proof.«deflate.c.engine.readbuf»')
            first = re.search(r'^error: ([^\n]+)', result.stdout, re.MULTILINE)
            hit = re.match(re.escape(str(proof)) + r':(\d+):', first.group(1)) if first else None
            resource = any(term in result.stdout.lower() for term in (
                'maximum recursion depth', 'maximum number of heartbeats',
                'deterministic timeout', 'interrupted', 'out of memory'))
            if result.returncode == 0 or hit is None or resource or not start <= int(hit.group(1)) < end:
                raise RuntimeError(label + ' survived or failed inconclusively:\n' + result.stdout)
            print('KILLED ' + label + ': ' + first.group(1)
                  + '; complete source equality passed; no resource failure', flush=True)


if __name__ == '__main__':
    main()
