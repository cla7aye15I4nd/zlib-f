#!/usr/bin/env python3
"""Actual flush macro regressions must fail the input-history frame proof."""
from pathlib import Path
import os
import re
import shutil
import subprocess
import tempfile


def main():
    root = Path(__file__).resolve().parents[2]
    source = Path('ZlibF/Zlib/deflate_base.c.lean')
    arguments = Path('ZlibF/Proof/deflate.c.engine.flush-arguments.lean')
    frame = Path('ZlibF/Proof/deflate.c.engine.flush-macro-frame.lean')
    originals = {p: (root / p).read_text() for p in (source, arguments, frame)}
    actual_store = 'wr s (fun d => { d with block_start := d.strstart.toUInt64.toInt64 })'
    named_store = 'wr s fun d => { d with block_start := d.strstart.toUInt64.toInt64 }'
    variants = (
        ('extra-lookahead-consumption', 'lookahead := d.lookahead - 1'),
        ('lost-window-pointer', 'window := .null'),
        ('lost-hash-head-pointer', 'head := .null'),
    )
    env = os.environ.copy()
    env['LC_ALL'] = 'C'

    def build(where, target):
        return subprocess.run(['lake', 'build', 'ZlibF.Proof.«' + target + '»'],
                              cwd=where, env=env, text=True, stdout=subprocess.PIPE,
                              stderr=subprocess.STDOUT, timeout=600)

    def success(result, label):
        if result.returncode:
            raise RuntimeError(label + ':\n' + result.stdout)

    with tempfile.TemporaryDirectory(prefix='deflate-flush-history-') as name:
        scratch = Path(name)
        for filename in ('lakefile.toml', 'lean-toolchain'):
            shutil.copy2(root / filename, scratch / filename)
        shutil.copytree(root / 'ZlibF', scratch / 'ZlibF')
        shutil.copytree(root / '.lake', scratch / '.lake')
        success(build(scratch, 'deflate.c.engine.flush-cut'), 'positive full content-boundary caller')
        print('baseline: actual all-branch flush restores the initialized no-deferred-byte content boundary', flush=True)
        for label, field in variants:
            left, body = originals[source].split('def FLUSH_BLOCK_ONLY (', 1)
            middle, right = body.split('/-- `FLUSH_BLOCK(s, last)', 1)
            if middle.count(actual_store) != 1 or originals[arguments].count(named_store) != 1:
                raise RuntimeError('ambiguous actual/named macro store')
            replacement = 'wr s (fun d => { d with block_start := d.strstart.toUInt64.toInt64, ' + field + ' })'
            (scratch / source).write_text(left + 'def FLUSH_BLOCK_ONLY (' + middle.replace(actual_store, replacement)
                                         + '/-- `FLUSH_BLOCK(s, last)' + right)
            text = originals[arguments].replace(named_store, replacement)
            gate = text.split('/-- At a real zero-credit block cutpoint', 1)[0]
            (scratch / arguments).write_text(gate + '\nend Zlib.Deflate.Engine.Proofs\n')
            success(build(scratch, 'deflate.c.engine.flush-arguments'), label + ' complete synchronized macro source equality')
            # Earlier publication theorems are not the negative target: retain
            # their checked argument/store helpers, then check the new frame.
            helpers = text.split('/-- `FLUSH_BLOCK_ONLY(s, last)`.', 1)[0]
            (scratch / arguments).write_text(helpers + '\nend Zlib.Deflate.Engine.Proofs\n')
            result = build(scratch, 'deflate.c.engine.flush-macro-frame')
            first = re.search(r'^error: ([^\n]+)', result.stdout, re.MULTILINE)
            hit = re.match(re.escape(str(frame)) + r':(\d+):', first.group(1)) if first else None
            start = originals[frame][:originals[frame].index('theorem flush_macro_frame_execution')].count('\n') + 1
            end = originals[frame][:originals[frame].index('theorem flush_macro_run_frame')].count('\n') + 1
            exhausted = any(word in result.stdout.lower() for word in
                            ('maximum recursion depth', 'maximum number of heartbeats',
                             'deterministic timeout', 'interrupted', 'out of memory'))
            if result.returncode == 0 or hit is None or not start <= int(hit.group(1)) < end or exhausted:
                raise RuntimeError(label + ' survived or failed outside actual macro frame execution:\n' + result.stdout)
            print('KILLED ' + label + ': ' + first.group(1)
                  + '; synchronized whole-macro source equality checks; no resource failure', flush=True)


if __name__ == '__main__':
    main()
