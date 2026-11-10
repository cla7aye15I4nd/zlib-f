#!/usr/bin/env python3
"""Reject wrong first-fill padding while complete source equality checks."""
from pathlib import Path
import os
import re
import shutil
import subprocess
import tempfile


def main():
    root = Path(__file__).resolve().parents[2]
    source = Path('ZlibF/Zlib/deflate_base.c.lean')
    fragment = Path('ZlibF/Proof/deflate.c.engine.fill-source.lean')
    proof = Path('ZlibF/Proof/deflate.c.engine.fill-initial.lean')
    lake = shutil.which('lake') or str(Path.home() / '.elan/bin/lake')
    env = dict(os.environ, LC_ALL='C')
    originals = {p: (root / p).read_text() for p in (source, fragment)}
    text = (root / proof).read_text()
    start = text[:text.index('theorem fill_high_water_empty')].count('\n') + 1
    end = text[:text.index('theorem fill_window_empty_initial')].count('\n') + 1
    write = 'memsetB (← padd d.window d.high_water.toNat) 0 init.toUInt32.toNat'
    cases = [('drop-padding', write, 'pure ()'),
             ('extra-padding-byte', write, write.replace('init.toUInt32.toNat', '(init.toUInt32.toNat + 1)'))]

    with tempfile.TemporaryDirectory(prefix='deflate-first-fill-') as directory:
        scratch = Path(directory)
        for name in ('lakefile.toml', 'lean-toolchain'):
            shutil.copy2(root / name, scratch / name)
        shutil.copytree(root / 'ZlibF', scratch / 'ZlibF')
        shutil.copytree(root / '.lake/build', scratch / '.lake/build')

        def build(module):
            return subprocess.run([lake, 'build', module], cwd=scratch, env=env,
                                  text=True, stdout=subprocess.PIPE,
                                  stderr=subprocess.STDOUT, timeout=180)

        def require(result, label):
            if result.returncode:
                raise RuntimeError(label + ':\n' + result.stdout)

        require(build('ZlibF.Proof.«deflate.c.engine.fill-initial»'), 'positive baseline')
        print('baseline: complete no-input first-fill execution checks', flush=True)
        for label, old, new in cases:
            for path, original in originals.items():
                if original.count(old) != 1:
                    raise RuntimeError('ambiguous mutation: ' + str(path))
                (scratch / path).write_text(original.replace(old, new))
            require(build('ZlibF.Proof.«deflate.c.engine.fill-source»'),
                    label + ' synchronized complete source equality')
            result = build('ZlibF.Proof.«deflate.c.engine.fill-initial»')
            error = re.search(r'^error: ([^\n]+)', result.stdout, re.MULTILINE)
            hit = re.match(re.escape(str(proof)) + r':(\d+):', error.group(1)) if error else None
            resource = any(word in result.stdout.lower() for word in
                           ('maximum recursion depth', 'maximum number of heartbeats',
                            'deterministic timeout', 'interrupted', 'out of memory'))
            if (result.returncode == 0 or hit is None or resource
                    or not start <= int(hit.group(1)) < end
                    or not any(word in result.stdout.lower() for word in
                               ('type mismatch', 'unsolved goals', 'not definitionally equal'))):
                raise RuntimeError(label + ' survived or failed inconclusively:\n' + result.stdout)
            print('KILLED ' + label + ': complete source equality checks; '
                  + error.group(1), flush=True)
        for path, original in originals.items():
            (scratch / path).write_text(original)
        require(build('ZlibF.Proof.«deflate.c.engine.slow-first»'), 'positive slow-strategy baseline')
        strategy = scratch / 'ZlibF/Zlib/deflate_strategies.c.lean'
        original = strategy.read_text()
        before, rest = original.split('def deflate_slow_body (', 1)
        body, after = rest.split('/-- `local block_state deflate_slow(', 1)
        old = 'if la < MIN_LOOKAHEAD_u && flush == Z_NO_FLUSH then'
        if body.count(old) != 1:
            raise RuntimeError('ambiguous slow return mutation')
        strategy.write_text(before + 'def deflate_slow_body ('
                            + body.replace(old, 'if la < 3 && flush == Z_NO_FLUSH then')
                            + '/-- `local block_state deflate_slow(' + after)
        require(build('ZlibF.Zlib.«deflate_strategies.c»'), 'mutated slow source compilation')
        result = build('ZlibF.Proof.«deflate.c.engine.slow-first»')
        error = re.search(r'^error: ([^\n]+)', result.stdout, re.MULTILINE)
        expected = 'ZlibF/Proof/deflate.c.engine.slow-first.lean'
        hit = re.match(re.escape(expected) + r':(\d+):', error.group(1)) if error else None
        text = (root / expected).read_text()
        start = text[:text.index('theorem slow_first_body')].count('\n') + 1
        end = text[:text.index('theorem slow_first_short_run')].count('\n') + 1
        resource = any(word in result.stdout.lower() for word in
                       ('maximum recursion depth', 'maximum number of heartbeats',
                        'deterministic timeout', 'interrupted', 'out of memory'))
        if (result.returncode == 0 or hit is None or resource
                or not start <= int(hit.group(1)) < end):
            raise RuntimeError('slow return mutant survived or failed elsewhere:\n' + result.stdout)
        print('KILLED slow-return-threshold: ' + error.group(1), flush=True)



if __name__ == '__main__':
    main()
