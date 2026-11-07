#!/usr/bin/env python3
"""The actual FINISH body must break precisely at the EOF stop cutpoint."""
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
    suffix = Path('ZlibF/Proof/deflate.c.engine.short-strategy-step.lean')
    proof = Path('ZlibF/Proof/deflate.c.engine.finish-strategy-step.lean')
    originals = {p: (root / p).read_text() for p in (source, fragment, suffix, proof)}
    old = 'if la == 0 then return { st with brk := true }'
    cases = (('inverted-eof-stop', 'if la != 0 then return { st with brk := true }'),
             ('dropped-eof-break', 'if la == 0 then return { st with brk := false }'))
    target = 'ZlibF.Proof.«deflate.c.engine.finish-strategy-step»'
    env = dict(os.environ, LC_ALL='C')
    with tempfile.TemporaryDirectory(prefix='deflate-finish-body-') as directory:
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

        require(build(target), 'positive complete actual FINISH body')
        print('baseline: actual refill, short decisions, EOF break and continuing rank check', flush=True)
        for label, new in cases:
            left, rest = originals[source].split('def deflate_slow_body (', 1)
            body, right = rest.split('/-- `local block_state deflate_slow(', 1)
            if body.count(old) != 1 or originals[fragment].count(old) != 1 or originals[suffix].count(old) != 1:
                raise RuntimeError('ambiguous synchronized FINISH stop mutation')
            (scratch / source).write_text(left + 'def deflate_slow_body (' + body.replace(old, new)
                                          + '/-- `local block_state deflate_slow(' + right)
            (scratch / fragment).write_text(originals[fragment].replace(old, new))
            (scratch / suffix).write_text(originals[suffix].replace(old, new))
            # Check source equalities without importing older execution proofs.
            # Inverting EOF also invalidates an earlier real fill-ready body
            # theorem; that is semantic rejection, not a source-equality gate.
            gate_path = Path('ZlibF/Proof/deflate.c.engine.finish-source-gate.lean')
            gate_text = originals[suffix].replace(old, new).split('/-- Initialized search and every decision', 1)[0]
            gate_text = gate_text.replace('import ZlibF.Proof.«deflate.c.engine.short-decisions»',
                                          'import ZlibF.Proof.«deflate.c.engine.slow-source»')
            gate_text = gate_text.replace('open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public',
                                          'open C Zlib.Deflate Zlib.Deflate.Spec')
            gate_text = gate_text.replace('open ZlibF.Math.DeflateSymbols\n', '')
            (scratch / gate_path).write_text(gate_text + '\nend Zlib.Deflate.Engine.Proofs\n')
            require(build('ZlibF.Proof.«deflate.c.engine.slow-source»',
                          'ZlibF.Proof.«deflate.c.engine.finish-source-gate»'),
                    label + ' whole-body and suffix source equalities')
            result = build(target)
            first = re.search(r'^error: ([^\n]+)', result.stdout, re.MULTILINE)
            expected = proof if label == 'dropped-eof-break' else Path('ZlibF/Proof/deflate.c.engine.slow-refill.lean')
            hit = re.match(re.escape(str(expected)) + r':(\d+):', first.group(1)) if first else None
            text = (root / expected).read_text()
            theorem = 'slow_finish_body_after_fill' if expected == proof else 'slow_body_fill_ready'
            next_theorem = 'slow_finish_strategy_step' if expected == proof else 'slow_body_fill_wait'
            start = text[:text.index('theorem ' + theorem)].count('\n') + 1
            end = text[:text.index('theorem ' + next_theorem)].count('\n') + 1
            resource = any(word in result.stdout.lower() for word in
                           ('maximum recursion depth', 'maximum number of heartbeats',
                            'deep recursion detected', 'deterministic timeout', 'interrupted', 'out of memory'))
            if result.returncode == 0 or hit is None or not start <= int(hit.group(1)) < end or resource:
                raise RuntimeError(label + ' survived or failed inconclusively:\n' + result.stdout)
            print('KILLED ' + label + ': ' + first.group(1)
                  + '; whole-body and suffix source equalities check; no resource failure', flush=True)


if __name__ == '__main__':
    main()
