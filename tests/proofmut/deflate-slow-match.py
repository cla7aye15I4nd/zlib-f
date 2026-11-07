#!/usr/bin/env python3
"""Reject synchronized mutations of actual slow match consumption."""
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
    module = 'ZlibF.Proof.«deflate.c.engine.slow-match»'
    cases = (
        ('match-counter-decrement',
         'wr s (fun d => { d with prev_length := d.prev_length - 1 })',
         'wr s (fun d => { d with prev_length := d.prev_length })',
         'match-insert', 'theorem slow_match_insert_step'),
        ('match-skipped-insertion',
         'if ss ≤ max_insert then INSERT_STRING s ss else pure hh',
         'if false then INSERT_STRING s ss else pure hh',
         'match-insert', 'theorem slow_match_insert_step'),
        ('match-final-position',
         'wr s (fun d => { d with match_available := 0, match_length := MIN_MATCH_u - 1, strstart := d.strstart + 1 })',
         'wr s (fun d => { d with match_available := 0, match_length := MIN_MATCH_u - 1, strstart := d.strstart + 2 })',
         'match-advance', 'theorem slow_match_advance'),
        ('match-lookahead-consumption',
         'wr s (fun d => { d with lookahead := d.lookahead - (d.prev_length - 1), prev_length := d.prev_length - 2 })',
         'wr s (fun d => { d with lookahead := d.lookahead - d.prev_length, prev_length := d.prev_length - 2 })',
         'match-advance', 'theorem slow_match_advance'),
        ('match-insertion-limit',
         'let max_insert : UInt32 := d.strstart + d.lookahead - MIN_MATCH_u',
         'let max_insert : UInt32 := d.strstart + d.prev_length - MIN_MATCH_u',
         'slow-match', 'theorem slow_match_before_flush'),
    )
    proof_texts = {name: (root / f'ZlibF/Proof/deflate.c.engine.{name}.lean').read_text()
                   for _, _, _, name, _ in cases}
    with tempfile.TemporaryDirectory(prefix='deflate-slow-match-') as directory:
        scratch = Path(directory)
        for name in ('lakefile.toml', 'lean-toolchain'):
            shutil.copy2(root / name, scratch / name)
        shutil.copytree(root / 'ZlibF', scratch / 'ZlibF')
        shutil.copytree(root / '.lake/build', scratch / '.lake/build')

        def build(*modules):
            return subprocess.run([lake, 'build', *modules], cwd=scratch, env=env, text=True,
                                  stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=180)

        def require(result, label):
            if result.returncode:
                raise RuntimeError(label + ':\n' + result.stdout)

        require(build(module), 'positive complete match-branch proof baseline')
        print('baseline: actual non-flushing match decision checks', flush=True)
        for label, old, new, name, theorem in cases:
            before, rest = original[source].split('def deflate_slow_body (', 1)
            body, after = rest.split('/-- `local block_state deflate_slow(', 1)
            if body.count(old) != 1 or original[fragment].count(old) != 1:
                raise RuntimeError('ambiguous synchronized mutation: ' + label)
            (scratch / source).write_text(before + 'def deflate_slow_body (' + body.replace(old, new)
                                          + '/-- `local block_state deflate_slow(' + after)
            (scratch / fragment).write_text(original[fragment].replace(old, new))
            require(build('ZlibF.Proof.«deflate.c.engine.slow-source»'),
                    label + ' complete source equality')
            result = build(module)
            error = re.search(r'^error: ([^\n]+)', result.stdout, re.MULTILINE)
            expected = f'ZlibF/Proof/deflate.c.engine.{name}.lean'
            hit = re.match(re.escape(expected) + r':(\d+):', error.group(1)) if error else None
            text = proof_texts[name]
            start = text[:text.index(theorem)].count('\n') + 1
            following = text.find('\ntheorem ', text.index(theorem) + len(theorem))
            end = len(text.splitlines()) + 1 if following < 0 else text[:following].count('\n') + 1
            resource = any(word in result.stdout.lower() for word in
                           ('maximum recursion depth', 'maximum number of heartbeats',
                            'deep recursion detected', 'deterministic timeout', 'interrupted', 'out of memory'))
            if (result.returncode == 0 or hit is None or resource
                    or not start <= int(hit.group(1)) < end):
                raise RuntimeError(label + ' survived or failed inconclusively:\n' + result.stdout)
            print('KILLED ' + label + ': ' + error.group(1), flush=True)


if __name__ == '__main__':
    main()
