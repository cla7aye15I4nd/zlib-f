#!/usr/bin/env python3
"""Reject actual strategy-refill mutants after full source equality checks."""
from pathlib import Path
import argparse
import os
import re
import shutil
import subprocess
import tempfile


def main():
    root = Path(__file__).resolve().parents[2]
    lake = shutil.which('lake') or str(Path.home() / '.elan/bin/lake')
    source = Path('ZlibF/Zlib/deflate_strategies.c.lean')
    fragment = Path('ZlibF/Proof/deflate.c.engine.slow-source.lean')
    proof = Path('ZlibF/Proof/deflate.c.engine.slow-refill.lean')
    originals = {p: (root / p).read_text() for p in (source, fragment)}
    guard = 'if la < MIN_LOOKAHEAD_u && flush == Z_NO_FLUSH then return { st with ret := some need_more }'
    cases = (
        ('refill-skipped', 'body', '    fill_window s', '    pure ()', 'slow_body_fill_ready'),
        ('refill-wait-dropped', 'body', guard,
         'if la < MIN_LOOKAHEAD_u && flush == Z_NO_FLUSH then pure ()', 'slow_body_fill_wait'),
        ('refill-wait-result', 'body', guard, guard.replace('some need_more', 'some block_done'), 'slow_body_fill_wait'),
        ('refill-ready-threshold', 'body', guard, guard.replace('la <', 'la ≤'), 'slow_body_fill_ready'),
        ('strategy-return-result', 'strategy', 'if let some r := st.ret then return r',
         'if let some r := st.ret then return block_done', 'slow_short_no_flush_boundary'),
    )
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--only', choices=[case[0] for case in cases])
    selected = parser.parse_args().only
    if selected:
        cases = tuple(case for case in cases if case[0] == selected)
    with tempfile.TemporaryDirectory(prefix='deflate-slow-refill-') as directory:
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

        caller = os.environ.get('ZLIBF_SLOW_REFILL_CALLER', 'slow-refill')
        require(build(caller), 'positive full no-flush iteration with actual refill')
        print('baseline: full no-flush iteration with actual refill checks', flush=True)
        for label, scope, old, new, theorem in cases:
            begin = 'def deflate_slow_body (' if scope == 'body' else 'def deflate_slow ('
            end = '\ndef deflate_slow (' if scope == 'body' else '/-! ## `deflate_rle` -/'
            before, body = originals[source].split(begin, 1)
            body, after = body.split(end, 1)
            if body.count(old) != 1 or (scope == 'body' and originals[fragment].count(old) != 1):
                raise RuntimeError('ambiguous synchronized mutation: ' + label)
            (scratch / source).write_text(before + begin + body.replace(old, new) + end + after)
            fragment_text = originals[fragment].replace(old, new) if scope == 'body' else originals[fragment]
            (scratch / fragment).write_text(fragment_text)
            require(build('slow-source'), label + ' complete body source equality')
            result = build('slow-refill')
            text = (root / proof).read_text()
            start = text[:text.index('theorem ' + theorem)].count('\n') + 1
            following = text.find('\ntheorem ', text.index('theorem ' + theorem) + len(theorem))
            end = len(text.splitlines()) + 1 if following < 0 else text[:following].count('\n') + 1
            errors = re.findall(r'^error: (' + re.escape(str(proof)) + r':(\d+):[^\n]*)',
                                result.stdout, re.MULTILINE)
            resource = any(term in result.stdout.lower() for term in (
                'maximum recursion depth', 'maximum number of heartbeats', 'deep recursion detected',
                'deterministic timeout', 'interrupted', 'out of memory'))
            hit = next((line for line, number in errors if start <= int(number) < end), None)
            if result.returncode == 0 or hit is None or resource:
                raise RuntimeError(label + ' survived or failed inconclusively:\n' + result.stdout)
            print('KILLED ' + label + ': ' + hit, flush=True)


if __name__ == '__main__':
    main()
