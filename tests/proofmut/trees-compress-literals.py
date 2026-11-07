#!/usr/bin/env python3
"""A dropped literal write must fail the actual fixed-payload proof.

Change the actual translation and its named source fragment together.
The whole-function source equality must still check. Resource failures
and failures outside the literal-body execution proof are not rejections.
"""
from pathlib import Path
import os
import re
import shutil
import subprocess
import tempfile


def main():
    root = Path(__file__).resolve().parents[2]
    source = Path('ZlibF/Zlib/trees.c.lean')
    fragments = Path('ZlibF/Proof/trees.c.compress-source.lean')
    proof = Path('ZlibF/Proof/trees.c.compress-literals.lean')
    original_source = (root / source).read_text()
    original_fragments = (root / fragments).read_text()
    proof_text = (root / proof).read_text()
    env = os.environ.copy()
    env['LC_ALL'] = 'C'

    def run(where, args):
        return subprocess.run(args, cwd=where, env=env, text=True,
                              stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=180)

    def require_success(result, label):
        if result.returncode:
            raise RuntimeError(label + ':\n' + result.stdout)

    with tempfile.TemporaryDirectory(prefix='trees-compress-literals-') as name:
        scratch = Path(name)
        for file in ('lakefile.toml', 'lean-toolchain'):
            shutil.copy2(root / file, scratch / file)
        shutil.copytree(root / 'ZlibF', scratch / 'ZlibF')
        shutil.copytree(root / '.lake', scratch / '.lake')
        build = ['lake', 'build', 'ZlibF.Proof.«trees.c.compress-literals»']
        require_success(run(scratch, build), 'baseline fixed-literal proof failed')
        print('baseline: complete fixed-literal payload and default-memory bound check', flush=True)

        left, body = original_source.split('def compress_block (', 1)
        body, right = body.split('/-- `local int detect_data_type', 1)
        old = 'if dist == 0 then\n          send_code s lc.toInt ltree'
        new = 'if dist == 0 then\n          pure ()'
        if body.count(old) != 1:
            raise RuntimeError('ambiguous actual literal-write mutation')
        (scratch / source).write_text(left + 'def compress_block (' + body.replace(old, new)
                                     + '/-- `local int detect_data_type' + right)
        old = 'if dist == 0 then\n    send_code s lc.toInt ltree'
        new = 'if dist == 0 then\n    pure ()'
        if original_fragments.count(old) != 1:
            raise RuntimeError('ambiguous named literal-write mutation')
        (scratch / fragments).write_text(original_fragments.replace(old, new))

        require_success(run(scratch, ['lake', 'build', 'ZlibF.Proof.«trees.c.compress-source»']),
                        'synchronized complete source equality failed')
        print('mutant: complete compress_block source equality still checks', flush=True)
        result = run(scratch, build)
        first = re.search(r'^error: ([^\n]+)', result.stdout, re.MULTILINE)
        hit = re.match(re.escape(str(proof)) + r':(\d+):', first.group(1)) if first else None
        start = proof_text[:proof_text.index('theorem cbFixedLiteralBody_run')].count('\n') + 1
        end = proof_text[:proof_text.index('theorem cbFixedLiteralLoop_run')].count('\n') + 1
        exhausted = any(word in result.stdout.lower() for word in
                        ('maximum recursion depth', 'maximum number of heartbeats',
                         'deterministic timeout', 'interrupted', 'out of memory'))
        if (result.returncode == 0 or hit is None or not start <= int(hit.group(1)) < end
                or exhausted or 'type mismatch' not in result.stdout.lower()):
            raise RuntimeError('mutant survived or lacked a local type rejection:\n' + result.stdout)
        print('KILLED dropped-literal-write: ' + first.group(1)
              + '; whole-source equality checks; no resource timeout', flush=True)


if __name__ == '__main__':
    main()
