#!/usr/bin/env python3
"""Reject block-tag, reset and final-alignment source regressions.

Actual C-translation bodies are mutated in scratch. For flush-block
mutants, the named fragments are synchronized and the complete source
equality must check before execution-proof rejection. Reset/alignment mutants fail
their actual callee execution proof. Resource failures are inconclusive.
"""
from pathlib import Path
import os
import re
import shutil
import subprocess
import sys
import tempfile


def main():
    root = Path(__file__).resolve().parents[2]
    lake = shutil.which('lake') or str(Path.home() / '.elan/bin/lake')
    source = Path('ZlibF/Zlib/trees.c.lean')
    cut = Path('ZlibF/Proof/trees.c.flush-source.lean')
    originals = {p: (root / p).read_text() for p in (source, cut)}
    cases = (
        ('end-marker-frequency', 'init', 'setFc (← pLtree s) END_BLOCK.toInt 1',
         'setFc (← pLtree s) END_BLOCK.toInt 0', 'trees.c.block', 'init_block_spec0'),
        ('reset-symbol-counter', 'init', 'md s fun d => { d with sym_next := 0 }',
         'md s fun d => { d with sym_next := 1 }', 'trees.c.block', 'init_block_spec0'),
        ('fixed-tag-type', 'flush', '(STATIC_TREES <<< 1) last', '(STATIC_TREES <<< 2) last',
         'deflate.c.engine.fixed-header', 'fixed_header_engine'),
        ('fixed-tag-width', 'flush', 'send_bits s (← iadd (STATIC_TREES <<< 1) last) 3',
         'send_bits s (← iadd (STATIC_TREES <<< 1) last) 2',
         'deflate.c.engine.fixed-header', 'fixed_header_engine'),
        ('drop-block-reset', 'flush', 'init_block s', 'pure ()',
         'deflate.c.engine.fixed-block', 'fixed_block_ready_frame'),
        ('wrong-final-alignment-gate', 'flush', 'if last != 0 then bi_windup s',
         'if last == 0 then bi_windup s', 'deflate.c.engine.fixed-block', 'fixed_block_ready_frame'),
        ('windup-cleared-count', 'windup', 'md s fun d => { d with bi_valid := 0 }',
         'md s fun d => { d with bi_valid := 1 }', 'trees.c.bits', 'bi_windup_big'),
    )
    selected = set(sys.argv[1:])
    if selected:
        unknown = selected - {x[0] for x in cases}
        if unknown:
            raise RuntimeError('unknown mutation labels: ' + ', '.join(sorted(unknown)))
        cases = tuple(x for x in cases if x[0] in selected)
    spans = {}
    for _, _, _, _, module, theorem in cases:
        path = Path('ZlibF/Proof/' + module + '.lean')
        text = (root / path).read_text()
        start = text[:text.index('theorem ' + theorem)].count('\n') + 1
        following = text.find('\ntheorem ', text.index('theorem ' + theorem) + len('theorem ' + theorem))
        end = len(text.splitlines()) + 1 if following < 0 else text[:following].count('\n') + 1
        spans[(module, theorem)] = (str(path), start, end)
    with tempfile.TemporaryDirectory(prefix='deflate-fixed-block-') as directory:
        scratch = Path(directory)
        for name in ('lakefile.toml', 'lean-toolchain'):
            shutil.copy2(root / name, scratch / name)
        shutil.copytree(root / 'ZlibF', scratch / 'ZlibF')
        shutil.copytree(root / '.lake/build', scratch / '.lake/build')

        def build(module):
            return subprocess.run([lake, 'build', module], cwd=scratch,
                                  env=dict(os.environ, LC_ALL='C'), text=True,
                                  stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=600)

        def require(result, label):
            if result.returncode:
                raise RuntimeError(label + ':\n' + result.stdout)

        require(build('ZlibF.Proof.«deflate.c.engine.fixed-block-output»'), 'positive complete fixed-block baseline')
        print('baseline: both block flags, actual reset/alignment/publication and independent raw validity', flush=True)
        for label, scope, old, new, module, theorem in cases:
            first, last = {
                'init': ('def init_block (', '/-- `void ZLIB_INTERNAL _tr_init'),
                'windup': ('def bi_windup (', '/-- `local void gen_codes'),
                'flush': ('def «_tr_flush_block» (', '/-- `int ZLIB_INTERNAL _tr_tally'),
            }[scope]
            left, body = originals[source].split(first, 1)
            body, right = body.split(last, 1)
            if body.count(old) != 1:
                raise RuntimeError('ambiguous actual mutation: ' + label)
            (scratch / source).write_text(left + first + body.replace(old, new) + last + right)
            changed = originals[cut]
            if scope == 'flush':
                if changed.count(old) != 1:
                    raise RuntimeError('ambiguous synchronized fragment: ' + label)
                changed = changed.replace(old, new)
            (scratch / cut).write_text(changed)
            require(build('ZlibF.Zlib.«trees.c»'), label + ' actual source compilation')
            if scope == 'flush':
                require(build('ZlibF.Proof.«trees.c.flush-source»'), label + ' complete source equality')
            result = build('ZlibF.Proof.«' + module + '»')
            first_error = re.search(r'^error: ([^\n]+)', result.stdout, re.MULTILINE)
            path, start, end = spans[(module, theorem)]
            hit = re.match(re.escape(path) + r':(\d+):', first_error.group(1)) if first_error else None
            exhausted = any(word in result.stdout.lower() for word in (
                'maximum recursion depth', 'maximum number of heartbeats', 'deep recursion detected',
                'deterministic timeout', 'interrupted', 'out of memory'))
            if result.returncode == 0 or hit is None or exhausted or not start <= int(hit.group(1)) < end:
                raise RuntimeError(label + ' survived or failed inconclusively:\n' + result.stdout)
            print('KILLED ' + label + ': ' + first_error.group(1), flush=True)


if __name__ == '__main__':
    main()
