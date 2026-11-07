#!/usr/bin/env python3
"""Reject actual public deflate trailer regressions in their execution proofs.

Synchronize the exact source fragments first. Whole-function equality must
still check. Resource failures and failures outside the affected proof
are inconclusive.
"""
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
    source = Path('ZlibF/Zlib/deflate.c.lean')
    cut = Path('ZlibF/Proof/deflate.c.engine.public-source.lean')
    writer = Path('ZlibF/Proof/deflate.c.engine.trailer-state.lean')
    tail = Path('ZlibF/Proof/deflate.c.engine.trailer-output.lean')
    originals = {p: (root / p).read_text() for p in (source, cut, writer, tail)}
    cases = (
        ('high-checksum-shift', writer, 'putShortMSB s (a >>> 16).toUInt32',
         'putShortMSB s (a >>> 15).toUInt32', 'trailer-state', 'zlib_trailer_write'),
        ('low-checksum-mask', writer, 'putShortMSB s (a &&& 0xffff).toUInt32',
         'putShortMSB s (a &&& 0xff).toUInt32', 'trailer-state', 'zlib_trailer_write'),
        ('checksum-word-order', writer,
         'putShortMSB s (a >>> 16).toUInt32\n  putShortMSB s (a &&& 0xffff).toUInt32',
         'putShortMSB s (a &&& 0xffff).toUInt32\n  putShortMSB s (a >>> 16).toUInt32',
         'trailer-state', 'zlib_trailer_write'),
        ('drop-trailer-copy', tail, '  flush_pending strm\n', '  pure ()\n',
         'trailer-output', 'zlib_trailer_publish'),
        ('keep-positive-wrapper', tail, 'let nw ← ineg w', 'let nw := w',
         'trailer-output', 'zlib_trailer_publish'),
        ('wrong-pending-return', tail, 'return if (← rd s (·.pending)) != 0 then Z_OK else Z_STREAM_END',
         'return if (← rd s (·.pending)) == 0 then Z_OK else Z_STREAM_END',
         'trailer-output', 'zlib_trailer_publish'),
        ('rewrite-finished-trailer', tail, 'if (← rd s (·.wrap)) ≤ 0 then return Z_STREAM_END',
         'if (← rd s (·.wrap)) < -1 then return Z_STREAM_END',
         'public-finish', 'public_finished_headers'),
    )
    selected = set(sys.argv[1:])
    if selected:
        unknown = selected - {x[0] for x in cases}
        if unknown:
            raise RuntimeError('unknown mutation labels: ' + ', '.join(sorted(unknown)))
        cases = tuple(x for x in cases if x[0] in selected)
    spans = {}
    for _, _, _, _, module, theorem in cases:
        p = Path('ZlibF/Proof/deflate.c.engine.' + module + '.lean')
        s = (root / p).read_text()
        start = s[:s.index('theorem ' + theorem)].count('\n') + 1
        following = s.find('\ntheorem ', s.index('theorem ' + theorem) + len('theorem ' + theorem))
        end = len(s.splitlines()) + 1 if following < 0 else s[:following].count('\n') + 1
        spans[(module, theorem)] = (str(p), start, end)

    def replace_scoped(text, first, last, old, new, label):
        before, body = text.split(first, 1)
        body, after = body.split(last, 1)
        # The word pair is indented two spaces further inside the source branch.
        if '\n' in old and old not in body:
            old = old.replace('\n  ', '\n    ')
            new = new.replace('\n  ', '\n    ')
        if body.count(old) != 1:
            raise RuntimeError('ambiguous synchronized mutation: ' + label)
        return before + first + body.replace(old, new) + last + after

    with tempfile.TemporaryDirectory(prefix='deflate-trailer-') as directory:
        scratch = Path(directory)
        for name in ('lakefile.toml', 'lean-toolchain'):
            shutil.copy2(root / name, scratch / name)
        shutil.copytree(root / 'ZlibF', scratch / 'ZlibF')
        shutil.copytree(root / '.lake/build', scratch / '.lake/build')

        def build(module):
            return subprocess.run([lake, 'build', module], cwd=scratch,
                                  env=dict(os.environ, LC_ALL='C'), text=True,
                                  stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=600)

        def require(result, label):
            if result.returncode:
                raise RuntimeError(label + ':\n' + result.stdout)

        caller = os.environ.get('ZLIBF_TRAILER_CALLER')
        require(build('ZlibF.Proof.«' + (caller or 'deflate.c.engine.public-finish-pending') + '»'),
                'positive public finish baseline')
        print('baseline: checksum bytes, partial public finish and no repeated trailer', flush=True)
        for label, helper, old, new, module, theorem in cases:
            for p, text in originals.items():
                (scratch / p).write_text(text)
            (scratch / source).write_text(replace_scoped(originals[source],
                '  -- if (flush != Z_FINISH)', '/-- `int ZEXPORT deflateParams(', old, new, label))
            (scratch / cut).write_text(replace_scoped(originals[cut],
                '  -- if (flush != Z_FINISH)', 'def publicZlibHeader (', old, new, label))
            first, last = ('def zlibTrailer (', 'def zlibTrailerBuffer (') if helper == writer else (
                'def publicFinishTail (', '/-- The actual post-header source')
            changed = replace_scoped(originals[helper], first, last, old, new, label)
            if label == 'rewrite-finished-trailer':
                # The positive-wrapper path is unchanged at wrapper=1. Supply
                # its elementary new guard fact, so rejection must reach the
                # negative-wrapper execution proof being tested.
                fact = 'show ¬ (1 : Int32) ≤ 0 from by decide'
                if changed.count(fact) != 1:
                    raise RuntimeError('ambiguous positive-path guard fact')
                changed = changed.replace(fact, 'show ¬ (1 : Int32) < -1 from by decide')
            (scratch / helper).write_text(changed)
            require(build('ZlibF.Zlib.«deflate.c»'), label + ' actual source compilation')
            require(build('ZlibF.Proof.«deflate.c.engine.public-source»'), label + ' complete source equality')
            result = build('ZlibF.Proof.«' + (caller or 'deflate.c.engine.' + module) + '»')
            error = re.search(r'^error: ([^\n]+)', result.stdout, re.MULTILINE)
            p, start, end = spans[(module, theorem)]
            hit = re.match(re.escape(p) + r':(\d+):', error.group(1)) if error else None
            resource = any(word in result.stdout.lower() for word in (
                'maximum recursion depth', 'maximum number of heartbeats', 'deep recursion detected',
                'deterministic timeout', 'interrupted', 'out of memory'))
            if result.returncode == 0 or hit is None or resource or not start <= int(hit.group(1)) < end:
                raise RuntimeError(label + ' survived or failed inconclusively:\n' + result.stdout)
            print('KILLED ' + label + ': ' + error.group(1), flush=True)


if __name__ == '__main__':
    main()
