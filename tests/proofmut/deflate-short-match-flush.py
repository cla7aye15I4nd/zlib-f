#!/usr/bin/env python3
"""The bounded selected match decision must publish a full nonfinal block."""
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
    fragment = Path('ZlibF/Proof/deflate.c.engine.slow-source.lean')
    gate = Path('ZlibF/Proof/deflate.c.engine.short-match-emit-boundary.lean')
    proof = Path('ZlibF/Proof/deflate.c.engine.short-match-decision.lean')
    originals = {p: (root / p).read_text() for p in (source, fragment, gate, proof)}
    old = 'if bflush then\n      if let some r := (← FLUSH_BLOCK s 0)'
    named = 'if bflush then\n        if let some r := (← FLUSH_BLOCK (some (.tab ds)) 0)'
    cases = (
        ('dropped-full-match-flush', 'if false then\n      if let some r := (← FLUSH_BLOCK s 0)',
         'if false then\n        if let some r := (← FLUSH_BLOCK (some (.tab ds)) 0)'),
        ('premature-final-match-block', 'if bflush then\n      if let some r := (← FLUSH_BLOCK s 1)',
         'if bflush then\n        if let some r := (← FLUSH_BLOCK (some (.tab ds)) 1)'),
    )
    caller = os.environ.get('ZLIBF_SHORT_MATCH_FLUSH_CALLER', 'deflate.c.engine.short-strategy-step')
    target = 'ZlibF.Proof.«' + caller + '»'
    env = dict(os.environ, LC_ALL='C')
    # The complete caller also imports the older full-match execution proof.
    # Either actual proof of this same C decision must reject the mutation.
    execution_spans = []
    for path, theorem in ((proof, 'slow_match_search_boundary'),
                          (Path('ZlibF/Proof/deflate.c.engine.slow-match-loop.lean'), 'slow_match_full_flush_loop')):
        text = (root / path).read_text()
        start = text[:text.index('theorem ' + theorem)].count('\n') + 1
        execution_spans.append((str(path), start, len(text.splitlines()) + 1))
    with tempfile.TemporaryDirectory(prefix='deflate-short-match-flush-') as directory:
        scratch = Path(directory)
        for name in ('lakefile.toml', 'lean-toolchain'):
            shutil.copy2(root / name, scratch / name)
        shutil.copytree(root / 'ZlibF', scratch / 'ZlibF')
        shutil.copytree(root / '.lake/build', scratch / '.lake/build')

        def build(*targets):
            return subprocess.run([lake, 'build', *targets], cwd=scratch, env=env, text=True,
                                  stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=600)

        def require(result, label):
            if result.returncode:
                raise RuntimeError(label + ':\n' + result.stdout)

        require(build(target), 'positive initialized search and every positive-lookahead decision')
        print('baseline: initialized search, every short decision and strategy boundary check', flush=True)
        for label, changed, named_changed in cases:
            left, rest = originals[source].split('def deflate_slow_body (', 1)
            body, right = rest.split('/-- `local block_state deflate_slow(', 1)
            if body.count(old) != 1 or originals[fragment].count(old) != 1 or originals[gate].count(named) != 1:
                raise RuntimeError('ambiguous synchronized bounded match flush mutation')
            (scratch / source).write_text(left + 'def deflate_slow_body (' + body.replace(old, changed)
                                          + '/-- `local block_state deflate_slow(' + right)
            (scratch / fragment).write_text(originals[fragment].replace(old, changed))
            (scratch / gate).write_text(originals[gate].replace(named, named_changed))
            require(build('ZlibF.Proof.«deflate.c.engine.slow-source»',
                          'ZlibF.Proof.«deflate.c.engine.short-match-emit-boundary»'),
                    label + ' complete body equality and selected prefix source equality')
            result = build(target)
            first = re.search(r'^error: ([^\n]+)', result.stdout, re.MULTILINE)
            hit = re.match(r'([^:]+):(\d+):', first.group(1)) if first else None
            expected = hit and any(hit.group(1) == path and start <= int(hit.group(2)) < end
                                   for path, start, end in execution_spans)
            resource = any(word in result.stdout.lower() for word in
                           ('maximum recursion depth', 'maximum number of heartbeats',
                            'deep recursion detected', 'deterministic timeout', 'interrupted', 'out of memory'))
            if result.returncode == 0 or not expected or resource:
                raise RuntimeError(label + ' survived or failed inconclusively:\n' + result.stdout)
            print('KILLED ' + label + ': ' + first.group(1)
                  + '; complete body and prefix source equality check; no resource failure', flush=True)


if __name__ == '__main__':
    main()
