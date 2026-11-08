#!/usr/bin/env python3
"""Require the nonfinal EOF proof to reject changed actual tail control."""
from pathlib import Path
import os
import re
import shutil
import subprocess
import tempfile


def main():
    root = Path(__file__).resolve().parents[2]
    lake = shutil.which('lake') or str(Path.home() / '.elan/bin/lake')
    source = Path('ZlibF/Zlib/deflate_strategies.c.lean')
    proof = Path('ZlibF/Proof/deflate.c.engine.nonfinal-eof-control.lean')
    original = (root / source).read_text()
    before, rest = original.split('def finish_tail (', 1)
    body, after = rest.split('/-! ## `deflate_stored` -/', 1)
    cases = (
        ('reversed-symbol-check', 'if (← rd s (·.sym_next)) != 0 then',
         'if (← rd s (·.sym_next)) == 0 then'),
        ('wrong-result', 'return block_done', 'return finish_done'),
        ('wrong-final-bit', 'FLUSH_BLOCK s 0', 'FLUSH_BLOCK s 1'),
    )
    text = (root / proof).read_text()
    start = text[:text.index('theorem finish_tail_nonfinal_boundary')].count('\n') + 1
    end = len(text.splitlines()) + 1
    env = dict(os.environ, LC_ALL='C')
    with tempfile.TemporaryDirectory(prefix='deflate-nonfinal-tail-') as directory:
        scratch = Path(directory)
        for name in ('lakefile.toml', 'lean-toolchain'):
            shutil.copy2(root / name, scratch / name)
        shutil.copytree(root / 'ZlibF', scratch / 'ZlibF')
        shutil.copytree(root / '.lake/build', scratch / '.lake/build')

        def build(target):
            return subprocess.run([lake, 'build', target], cwd=scratch, env=env,
                                  text=True, stdout=subprocess.PIPE,
                                  stderr=subprocess.STDOUT, timeout=600)

        def require(result, label):
            if result.returncode:
                raise RuntimeError(label + ':\n' + result.stdout)

        require(build('ZlibF.Proof.«deflate.c.engine.positive-nonfinal-call»'),
                'positive complete nonfinal strategy caller')
        print('baseline: complete nonfinal strategy caller checks', flush=True)
        for label, old, new in cases:
            if body.count(old) != 1:
                raise RuntimeError('ambiguous tail mutation: ' + label)
            (scratch / source).write_text(before + 'def finish_tail (' + body.replace(old, new)
                                          + '/-! ## `deflate_stored` -/' + after)
            require(build('ZlibF.Zlib.«deflate_strategies.c»'), label + ' translated source compilation')
            result = build('ZlibF.Proof.«deflate.c.engine.nonfinal-eof-control»')
            errors = re.findall(r'^error: (' + re.escape(str(proof)) + r':(\d+):[^\n]*)',
                                result.stdout, re.MULTILINE)
            hit = next((line for line, number in errors if start <= int(number) < end), None)
            resource = any(term in result.stdout.lower() for term in (
                'maximum recursion depth', 'maximum number of heartbeats', 'deep recursion detected',
                'deterministic timeout', 'interrupted', 'out of memory'))
            if result.returncode == 0 or hit is None or resource:
                raise RuntimeError(label + ' survived or failed inconclusively:\n' + result.stdout)
            print('KILLED ' + label + ': ' + hit + '; source compiles; no resource failure', flush=True)


if __name__ == '__main__':
    main()
