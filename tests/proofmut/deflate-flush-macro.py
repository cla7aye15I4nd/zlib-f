#!/usr/bin/env python3
"""Real FLUSH_BLOCK_ONLY pointer, signed length and block-start regressions fail locally."""
from pathlib import Path
import os
import re
import shutil
import subprocess
import tempfile


def main():
    root = Path(__file__).resolve().parents[2]
    source = Path('ZlibF/Zlib/deflate_base.c.lean')
    proof = Path('ZlibF/Proof/deflate.c.engine.flush-arguments.lean')
    originals = {p: (root / p).read_text() for p in (source, proof)}
    variants = (
        ('source-offset-plus-one', 'd.block_start.toUInt64.toUInt32.toNat',
         '(d.block_start.toUInt64.toUInt32.toNat + 1)', 'default_flush_arguments', 'flush_block_start_engine'),
        ('reversed-signed-length', 'lsub d.strstart.toUInt64.toInt64 d.block_start',
         'lsub d.block_start d.strstart.toUInt64.toInt64', 'default_flush_arguments', 'flush_block_start_engine'),
        ('dropped-block-start-update', 'wr s (fun d => { d with block_start := d.strstart.toUInt64.toInt64 })',
         'pure ()', 'flush_block_only_publish', 'flush_block_only_final_valid'),
    )
    env = os.environ.copy()
    env['LC_ALL'] = 'C'

    def build(where):
        return subprocess.run(['lake', 'build', 'ZlibF.Proof.«deflate.c.engine.flush-arguments»'],
                              cwd=where, env=env, text=True, stdout=subprocess.PIPE,
                              stderr=subprocess.STDOUT, timeout=600)

    def success(result, label):
        if result.returncode:
            raise RuntimeError(label + ':\n' + result.stdout)

    with tempfile.TemporaryDirectory(prefix='deflate-flush-macro-') as name:
        scratch = Path(name)
        for filename in ('lakefile.toml', 'lean-toolchain'):
            shutil.copy2(root / filename, scratch / filename)
        shutil.copytree(root / 'ZlibF', scratch / 'ZlibF')
        shutil.copytree(root / '.lake', scratch / '.lake')
        success(build(scratch), 'positive actual full macro/publication/raw validity')
        print('baseline: complete real macro and terminal independent raw validity check', flush=True)
        for label, old, new, first_name, last_name in variants:
            left, body = originals[source].split('def FLUSH_BLOCK_ONLY (', 1)
            middle, right = body.split('/-- `FLUSH_BLOCK(s, last)', 1)
            if middle.count(old) != 1:
                raise RuntimeError('ambiguous actual macro mutation')
            (scratch / source).write_text(left + 'def FLUSH_BLOCK_ONLY (' + middle.replace(old, new)
                                         + '/-- `FLUSH_BLOCK(s, last)' + right)
            text = originals[proof]
            if label == 'dropped-block-start-update':
                model_old = 'wr s fun d => { d with block_start := d.strstart.toUInt64.toInt64 }'
                if text.count(model_old) != 1:
                    raise RuntimeError('ambiguous whole macro source equality')
                text = text.replace(model_old, new)
            else:
                prefix, tail = text.split('/-- Naming the argument prefix', 1)
                if prefix.count(old) != 1:
                    raise RuntimeError('ambiguous named argument prefix')
                text = prefix.replace(old, new) + '/-- Naming the argument prefix' + tail
            marker = '/-- At a real zero-credit block cutpoint'
            (scratch / proof).write_text(text.split(marker, 1)[0] + '\nend Zlib.Deflate.Engine.Proofs\n')
            success(build(scratch), label + ' synchronized complete macro source equality')
            (scratch / proof).write_text(text)
            start = text[:text.index('theorem ' + first_name)].count('\n') + 1
            end = text[:text.index('theorem ' + last_name)].count('\n') + 1
            result = build(scratch)
            first = re.search(r'^error: ([^\n]+)', result.stdout, re.MULTILINE)
            hit = re.match(re.escape(str(proof)) + r':(\d+):', first.group(1)) if first else None
            exhausted = any(word in result.stdout.lower() for word in
                            ('maximum recursion depth', 'maximum number of heartbeats',
                             'deterministic timeout', 'interrupted', 'out of memory'))
            if result.returncode == 0 or hit is None or not start <= int(hit.group(1)) < end or exhausted:
                raise RuntimeError(label + ' survived or failed outside actual macro execution:\n' + result.stdout)
            print('KILLED ' + label + ': ' + first.group(1)
                  + '; synchronized full macro source equality checks; no resource failure', flush=True)


if __name__ == '__main__':
    main()
