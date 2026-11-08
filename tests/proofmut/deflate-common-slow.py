#!/usr/bin/env python3
"""Changing a real nondefault dispatch row must reject its slow-call proof."""
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
    original = (root / source).read_text()
    proof = Path('ZlibF/Proof/deflate.c.engine.common-slow-source.lean')
    text = (root / proof).read_text()
    start = text.index('theorem common_slow_config_func')
    end = text.index('\nset_option ', start)
    first_line = text[:start].count('\n') + 1
    last_line = text[:end].count('\n') + 1
    caller = 'ZlibF.Proof.«deflate.c.engine.common-initial-slow-finish»'
    env = dict(os.environ, LC_ALL='C')
    cases = (
        ('level-four-dispatch', '⟨4, 4, 16, 16, .slow⟩', '⟨4, 4, 16, 16, .fast⟩'),
        ('level-nine-dispatch', '⟨32, 258, 258, 4096, .slow⟩', '⟨32, 258, 258, 4096, .fast⟩'),
    )
    with tempfile.TemporaryDirectory(prefix='deflate-common-slow-') as directory:
        scratch = Path(directory)
        for name in ('lakefile.toml', 'lean-toolchain'):
            shutil.copy2(root / name, scratch / name)
        shutil.copytree(root / 'ZlibF', scratch / 'ZlibF')
        shutil.copytree(root / '.lake/build', scratch / '.lake/build')

        def build(target):
            return subprocess.run([lake, 'build', target], cwd=scratch, env=env,
                                  text=True, stdout=subprocess.PIPE,
                                  stderr=subprocess.STDOUT, timeout=900)

        def require(result, label):
            if result.returncode:
                raise RuntimeError(label + ':\n' + result.stdout)

        require(build(caller), 'positive initialized common slow caller')
        print('baseline: actual init, split header and complete public FINISH check', flush=True)
        for label, old, new in cases:
            if original.count(old) != 1:
                raise RuntimeError('mutation must match exactly once: ' + label)
            (scratch / source).write_text(original.replace(old, new, 1))
            require(build('ZlibF.Zlib.«deflate.c»'), label + ' actual translation compilation')
            result = build(caller)
            error = re.search(r'^error: ([^\n]+)', result.stdout, re.MULTILINE)
            hit = re.match(r'([^:]+):(\d+):', error.group(1)) if error else None
            designated = hit and hit.group(1) == str(proof) and first_line <= int(hit.group(2)) < last_line
            resource = any(word in result.stdout.lower() for word in (
                'maximum recursion depth', 'maximum number of heartbeats',
                'deep recursion detected', 'deterministic timeout', 'interrupted', 'out of memory'))
            if result.returncode == 0 or not designated or resource:
                raise RuntimeError(label + ' survived or failed inconclusively:\n' + result.stdout)
            print('KILLED ' + label + ': ' + error.group(1)
                  + '; mutated actual translation compiles; no resource failure', flush=True)
            (scratch / source).write_text(original)
            require(build(caller), label + ' restored positive initialized caller')


if __name__ == '__main__':
    main()
