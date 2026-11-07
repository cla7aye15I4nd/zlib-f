#!/usr/bin/env python3
"""Reject sliding mutants after both complete source equalities check."""
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
    whole = Path('ZlibF/Proof/deflate.c.engine.fill-source.lean')
    sliding = Path('ZlibF/Proof/deflate.c.engine.fill-slide-source.lean')
    proof = Path('ZlibF/Proof/deflate.c.engine.fill-slide-run.lean')
    originals = {path: (root / path).read_text() for path in (source, whole, sliding)}
    cases = (
        ('slide-source-offset',
         'memcpyB d.window (← padd d.window wsize.toNat) (wsize - more).toNat',
         'memcpyB d.window (← padd d.window (wsize.toNat + 1)) (wsize - more).toNat'),
        ('slide-copy-count',
         'memcpyB d.window (← padd d.window wsize.toNat) (wsize - more).toNat',
         'memcpyB d.window (← padd d.window wsize.toNat) ((wsize - more).toNat + 1)'),
        ('slide-match-position',
         'wr s (fun d => { d with match_start := d.match_start - wsize })',
         'wr s (fun d => { d with match_start := d.match_start })'),
        ('slide-current-position',
         'wr s (fun d => { d with strstart := d.strstart - wsize })',
         'wr s (fun d => { d with strstart := d.strstart })'),
        ('slide-signed-direction',
         'let block_start ← lsub (← rd s (·.block_start)) wsize.toUInt64.toInt64',
         'let block_start ← ladd (← rd s (·.block_start)) wsize.toUInt64.toInt64'),
        ('slide-insertion-clamp',
         'wr s (fun d => { d with insert := if d.insert > d.strstart then d.strstart else d.insert })',
         'wr s (fun d => { d with insert := if d.insert < d.strstart then d.strstart else d.insert })'),
        ('slide-drop-hash-loops', 'slide_hash s', 'pure ()'),
    )
    with tempfile.TemporaryDirectory(prefix='deflate-fill-slide-') as directory:
        scratch = Path(directory)
        for name in ('lakefile.toml', 'lean-toolchain'):
            shutil.copy2(root / name, scratch / name)
        shutil.copytree(root / 'ZlibF', scratch / 'ZlibF')
        shutil.copytree(root / '.lake/build', scratch / '.lake/build')

        def build(module):
            return subprocess.run([lake, 'build', 'ZlibF.Proof.«deflate.c.engine.' + module + '»'],
                                  cwd=scratch, env=dict(os.environ, LC_ALL='C'), text=True,
                                  stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=240)

        def require(result, label):
            if result.returncode:
                raise RuntimeError(label + ':\n' + result.stdout)

        require(build('fill-slide-empty'), 'positive complete sliding calls')
        print('baseline: actual empty and nonempty sliding calls check', flush=True)
        text = (root / proof).read_text()
        start = text[:text.index('theorem fill_slide_run')].count('\n') + 1
        for label, old, new in cases:
            before, body = originals[source].split('def fill_window (', 1)
            body, after = body.split('/-! ## `putShortMSB`, `flush_pending` -/', 1)
            if (body.count(old) != 1 or originals[whole].count(old) != 1
                    or originals[sliding].count(old) != 1):
                raise RuntimeError('ambiguous synchronized mutation: ' + label)
            (scratch / source).write_text(before + 'def fill_window (' + body.replace(old, new)
                                          + '/-! ## `putShortMSB`, `flush_pending` -/' + after)
            (scratch / whole).write_text(originals[whole].replace(old, new))
            (scratch / sliding).write_text(originals[sliding].replace(old, new))
            require(build('fill-slide-source'), label + ' both complete source equalities')
            result = build('fill-slide-run')
            error = re.search(r'^error: ([^\n]+)', result.stdout, re.MULTILINE)
            hit = re.match(re.escape(str(proof)) + r':(\d+):', error.group(1)) if error else None
            resource = any(term in result.stdout.lower() for term in (
                'maximum recursion depth', 'maximum number of heartbeats', 'deep recursion detected',
                'deterministic timeout', 'interrupted', 'out of memory'))
            if result.returncode == 0 or hit is None or resource or int(hit.group(1)) < start:
                raise RuntimeError(label + ' survived or failed inconclusively:\n' + result.stdout)
            print('KILLED ' + label + ': ' + error.group(1), flush=True)


if __name__ == '__main__':
    main()
