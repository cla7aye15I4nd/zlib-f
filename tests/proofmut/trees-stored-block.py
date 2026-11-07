#!/usr/bin/env python3
"""Stored-block source mutants fail their matching concrete execution proof."""
from pathlib import Path
import os
import re
import shutil
import subprocess
import tempfile


def main():
    root = Path(__file__).resolve().parents[2]
    source = Path('ZlibF/Zlib/trees.c.lean')
    header = Path('ZlibF/Proof/trees.c.stored-header.lean')
    copy = Path('ZlibF/Proof/trees.c.stored-copy.lean')
    originals = {p: (root / p).read_text() for p in (source, header, copy)}
    env = os.environ.copy()
    env['LC_ALL'] = 'C'

    def build(where, target):
        return subprocess.run(['lake', 'build', 'ZlibF.Proof.«' + target + '»'], cwd=where,
                              env=env, text=True, stdout=subprocess.PIPE,
                              stderr=subprocess.STDOUT, timeout=180)

    def success(result, label):
        if result.returncode:
            raise RuntimeError(label + ':\n' + result.stdout)

    variants = (
        ('length-complement', header, 'put_short s (~~~stored_len).toUInt16',
         'put_short s stored_len.toUInt16', 'put_short s (~~~length).toUInt16',
         'put_short s length.toUInt16', 'def storedHeaderBits', 'stored_block_header_emit'),
        ('dropped-pending-count', copy, 'pending := d.pending + stored_len',
         'pending := d.pending', 'pending := d.pending + length',
         'pending := d.pending', '/-- The actual copy reads', 'stored_block_copy_run'),
    )
    with tempfile.TemporaryDirectory(prefix='trees-stored-block-') as name:
        scratch = Path(name)
        for filename in ('lakefile.toml', 'lean-toolchain'):
            shutil.copy2(root / filename, scratch / filename)
        shutil.copytree(root / 'ZlibF', scratch / 'ZlibF')
        shutil.copytree(root / '.lake', scratch / '.lake')
        success(build(scratch, 'trees.c.stored-block'), 'positive complete stored writer')
        print('baseline: complete actual stored-block writer and source bytes check', flush=True)
        for label, proof, c_old, c_new, old, new, gate_end, theorem in variants:
            for path, text in originals.items():
                if path == source:
                    left, body = text.split('def «_tr_stored_block»', 1)
                    middle, right = body.split('/-- `void ZLIB_INTERNAL _tr_flush_bits', 1)
                    if middle.count(c_old) != 1:
                        raise RuntimeError('ambiguous actual stored-block mutation')
                    text = left + 'def «_tr_stored_block»' + middle.replace(c_old, c_new)
                    text += '/-- `void ZLIB_INTERNAL _tr_flush_bits' + right
                if label == 'dropped-pending-count' and path == header:
                    if text.count(old) != 1:
                        raise RuntimeError('ambiguous synchronized whole stored source')
                    text = text.replace(old, new)
                if path == proof:
                    prefix, tail = text.split(gate_end, 1)
                    if prefix.count(old) != 1:
                        raise RuntimeError('ambiguous stored fragment mutation')
                    text = prefix.replace(old, new) + gate_end + tail
                (scratch / path).write_text(text)
            changed = (scratch / proof).read_text()
            module = proof.stem
            (scratch / proof).write_text(changed.split(gate_end, 1)[0] + '\nend Zlib.Trees.Proofs.Out\n')
            success(build(scratch, module), label + ' complete source equality')
            (scratch / proof).write_text(changed)
            start = changed[:changed.index('theorem ' + theorem)].count('\n') + 1
            end_marker = 'def sourceByteBits' if proof == copy else 'end Zlib.Trees.Proofs.Out'
            end = changed[:changed.index(end_marker)].count('\n') + 1
            result = build(scratch, module)
            first = re.search(r'^error: ([^\n]+)', result.stdout, re.MULTILINE)
            hit = re.match(re.escape(str(proof)) + r':(\d+):', first.group(1)) if first else None
            exhausted = any(word in result.stdout.lower() for word in
                            ('maximum recursion depth', 'maximum number of heartbeats',
                             'deterministic timeout', 'interrupted', 'out of memory'))
            if result.returncode == 0 or hit is None or not start <= int(hit.group(1)) < end or exhausted:
                raise RuntimeError(label + ' survived or failed outside its execution proof:\n' + result.stdout)
            print('KILLED ' + label + ': ' + first.group(1)
                  + '; complete synchronized stored source checks; no resource failure', flush=True)


if __name__ == '__main__':
    main()
