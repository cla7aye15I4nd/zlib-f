#!/usr/bin/env python3
"""Reject actual EOF match-consumption mutations in the bounded proofs."""
from pathlib import Path
import os
import re
import shutil
import subprocess
import tempfile


def main():
    root = Path(__file__).resolve().parents[2]
    lake = shutil.which('lake') or str(Path.home() / '.elan/bin/lake')
    env = dict(os.environ, LC_ALL='C')
    source = Path('ZlibF/Zlib/deflate_strategies.c.lean')
    fragment = Path('ZlibF/Proof/deflate.c.engine.slow-source.lean')
    original = {p: (root / p).read_text() for p in (source, fragment)}
    frontier = env.get('ZLIBF_SHORT_MATCH_CALLER') == 'frontier'
    words = env.get('ZLIBF_SHORT_MATCH_CALLER') == 'words'
    target = 'ZlibF.Proof.«deflate.c.engine.' + ('short-match-words' if words else 'short-match-frontier' if frontier else 'short-match-advance') + '»'
    cases = (
        ('counter-not-decremented',
         'wr s (fun d => { d with prev_length := d.prev_length - 1 })',
         'wr s (fun d => { d with prev_length := d.prev_length })', 'short-match-insert'),
        ('insert-beyond-valid-input',
         'if ss ≤ max_insert then INSERT_STRING s ss else pure hh',
         'if true then INSERT_STRING s ss else pure hh', 'short-match-insert'),
        ('skip-last-valid-key',
         'if ss ≤ max_insert then INSERT_STRING s ss else pure hh',
         'if ss < max_insert then INSERT_STRING s ss else pure hh', 'short-match-insert'),
        ('final-position-plus-two',
         'wr s (fun d => { d with match_available := 0, match_length := MIN_MATCH_u - 1, strstart := d.strstart + 1 })',
         'wr s (fun d => { d with match_available := 0, match_length := MIN_MATCH_u - 1, strstart := d.strstart + 2 })',
         'short-match-advance'),
        ('consume-one-extra-byte',
         'wr s (fun d => { d with lookahead := d.lookahead - (d.prev_length - 1), prev_length := d.prev_length - 2 })',
         'wr s (fun d => { d with lookahead := d.lookahead - d.prev_length, prev_length := d.prev_length - 2 })',
         'short-match-advance'),
    )
    if words:
        cases = tuple(case for case in cases if case[0] in ('counter-not-decremented', 'insert-beyond-valid-input'))
    with tempfile.TemporaryDirectory(prefix='deflate-short-match-') as directory:
        scratch = Path(directory)
        for name in ('lakefile.toml', 'lean-toolchain'):
            shutil.copy2(root / name, scratch / name)
        shutil.copytree(root / 'ZlibF', scratch / 'ZlibF')
        shutil.copytree(root / '.lake/build', scratch / '.lake/build')

        def build(*modules):
            return subprocess.run([lake, 'build', *modules], cwd=scratch, env=env, text=True,
                                  stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=600)

        def require(result, label):
            if result.returncode:
                raise RuntimeError(label + ':\n' + result.stdout)

        require(build(target), 'complete bounded match-consumption baseline')
        print('baseline: complete bounded actual consumption checks', flush=True)
        # Older long-input execution proofs are not the negative-test gate.
        # Retain their definitions and pure lemmas, dropping only later
        # source execution theorems in this disposable scratch dependency graph.
        cuts = (
            ('match-insert', '/-- The loop increments strstart'),
            ('match-insert-loop', 'set_option maxHeartbeats'),
            ('match-advance', 'set_option maxHeartbeats'),
        )
        if frontier or words:
            cuts += (('short-match-insert', '/-- A consumed position'),
                     ('short-match-loop', 'set_option maxHeartbeats'),
                     ('short-match-advance', 'set_option maxHeartbeats'))
        for name, marker in cuts:
            path = scratch / f'ZlibF/Proof/deflate.c.engine.{name}.lean'
            text = path.read_text()
            if marker not in text:
                raise RuntimeError('missing independent bounded-proof cut: ' + name)
            path.write_text(text.split(marker, 1)[0] + '\nend Zlib.Deflate.Engine.Proofs\n')
        require(build(target), 'bounded proof without older long-input execution proofs')
        print('independent baseline: older long-input execution proofs excluded', flush=True)
        for label, old, new, name in cases:
            before, rest = original[source].split('def deflate_slow_body (', 1)
            body, after = rest.split('/-- `local block_state deflate_slow(', 1)
            if body.count(old) != 1 or original[fragment].count(old) != 1:
                raise RuntimeError('ambiguous synchronized source mutation: ' + label)
            (scratch / source).write_text(before + 'def deflate_slow_body (' + body.replace(old, new)
                                          + '/-- `local block_state deflate_slow(' + after)
            (scratch / fragment).write_text(original[fragment].replace(old, new))
            require(build('ZlibF.Proof.«deflate.c.engine.slow-source»'),
                    label + ' complete actual source equality')
            result = build(target)
            first = re.search(r'^error: ([^\n]+)', result.stdout, re.MULTILINE)
            if frontier:
                name = 'short-match-frontier-step' if name == 'short-match-insert' else 'short-match-frontier'
            if words:
                name = 'short-match-words'
            expected = Path(f'ZlibF/Proof/deflate.c.engine.{name}.lean')
            hit = re.match(re.escape(str(expected)) + r':(\d+):', first.group(1)) if first else None
            text = (scratch / expected).read_text()
            theorem = 'theorem slow_match_insert_step_at' if name == 'short-match-insert' else 'theorem slow_match_advance_bounded'
            if frontier:
                theorem = 'theorem slow_match_insert_step_frontier' if name == 'short-match-frontier-step' else 'theorem slow_match_advance_frontier'
            if words:
                theorem = 'theorem slow_match_two_remaining'
            start = text[:text.index(theorem)].count('\n') + 1
            resource = any(word in result.stdout.lower() for word in
                           ('maximum recursion depth', 'maximum number of heartbeats',
                            'deep recursion detected', 'deterministic timeout', 'interrupted', 'out of memory'))
            if result.returncode == 0 or hit is None or int(hit.group(1)) < start or resource:
                raise RuntimeError(label + ' survived or failed inconclusively:\n' + result.stdout)
            print('KILLED ' + label + ': ' + first.group(1)
                  + '; full source equality checks; bounded execution proof; no resource failure', flush=True)


if __name__ == '__main__':
    main()
