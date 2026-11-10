#!/usr/bin/env python3
"""Reject source-control mutations with the complete slow-loop proof imported.

Body variants synchronize the named source fragment first. A rejection counts
only inside an execution theorem for the affected function. Resource failures
and errors outside those proofs are inconclusive.
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
    env = dict(os.environ, LC_ALL='C')
    source = Path('ZlibF/Zlib/deflate_strategies.c.lean')
    fragment = Path('ZlibF/Proof/deflate.c.engine.slow-source.lean')
    originals = {p: (root / p).read_text() for p in (source, fragment)}
    module = os.environ.get('ZLIBF_SLOW_LOOP_CALLER', 'ZlibF.Proof.«deflate.c.engine.loop-entry»')
    loop = 'let st ← cwhile forever (deflate_slow_body s flush) {}'
    whole_proofs = (
        ('slow-refill', 'slow_short_no_flush_boundary'),
        ('content-refill', 'slow_short_content_boundary'),
        ('slow-loop', 'deflate_slow_no_flush_before_block'),
        ('strategy-no-flush-loop', 'deflate_slow_no_flush_full'),
    )
    cases = (
        ('wrong-result', 'strategy', 'if let some r := st.ret then return r',
         'if let some _ := st.ret then return block_done', whole_proofs),
        ('initial-return', 'strategy', loop,
         'let st ← cwhile forever (deflate_slow_body s flush) { ret := some block_done }', whole_proofs),
        ('wrong-flush', 'strategy', loop,
         'let st ← cwhile forever (deflate_slow_body s Z_FINISH) {}', whole_proofs),
        ('bypass-loop', 'strategy', loop,
         'let st : LoopS := { ret := some need_more }', whole_proofs),
        ('ignore-return', 'condition',
         'pure (!(st.brk || st.ret.isSome), st)', 'pure (!st.brk, st)', whole_proofs),
        ('refill-threshold', 'body',
         'if la < MIN_LOOKAHEAD_u && flush == Z_NO_FLUSH then return { st with ret := some need_more }',
         'if la <= MIN_LOOKAHEAD_u && flush == Z_NO_FLUSH then return { st with ret := some need_more }',
         (('slow-refill', 'slow_body_fill_ready'), ('slow-refill', 'slow_body_fill_wait'))),
        ('output-return', 'body',
         'if (← zrd d.strm (·.avail_out)) == 0 then return { st with hash_head, bflush, ret := some need_more }',
         'if (← zrd d.strm (·.avail_out)) != 0 then return { st with hash_head, bflush, ret := some need_more }',
         (('slow-literal', 'slow_literal_boundary'),)),
    )
    selection = set(sys.argv[1:])
    if selection:
        unknown = selection - {case[0] for case in cases}
        if unknown:
            raise RuntimeError('unknown mutation labels: ' + ', '.join(sorted(unknown)))
        cases = tuple(case for case in cases if case[0] in selection)
    spans = {}
    for _, _, _, _, proofs in cases:
        for proof, theorem in proofs:
            path = 'ZlibF/Proof/deflate.c.engine.' + proof + '.lean'
            text = (root / path).read_text()
            anchor = 'theorem ' + theorem
            start = text[:text.index(anchor)].count('\n') + 1
            following = text.find('\ntheorem ', text.index(anchor) + len(anchor))
            end = len(text.splitlines()) + 1 if following < 0 else text[:following].count('\n') + 1
            spans[(proof, theorem)] = (path, start, end)
    with tempfile.TemporaryDirectory(prefix='deflate-slow-loop-') as directory:
        scratch = Path(directory)
        for name in ('lakefile.toml', 'lean-toolchain'):
            shutil.copy2(root / name, scratch / name)
        shutil.copytree(root / 'ZlibF', scratch / 'ZlibF')
        shutil.copytree(root / '.lake/build', scratch / '.lake/build')

        def build(*modules):
            return subprocess.run([lake, 'build', *modules], cwd=scratch, env=env,
                                  text=True, stdout=subprocess.PIPE,
                                  stderr=subprocess.STDOUT, timeout=240)

        def require(result, label):
            if result.returncode:
                raise RuntimeError(label + ':\n' + result.stdout)

        require(build(module), 'positive initialized complete slow-loop baseline')
        print('baseline: selected complete slow-loop proof caller checks', flush=True)
        for label, scope, old, new, proofs in cases:
            for path, original in originals.items():
                (scratch / path).write_text(original)
            original = originals[source]
            if scope == 'condition':
                before, body, after = '', original, ''
            elif scope == 'body':
                before, rest = original.split('def deflate_slow_body (', 1)
                before += 'def deflate_slow_body ('
                body, after = rest.split('/-- `local block_state deflate_slow(', 1)
                after = '/-- `local block_state deflate_slow(' + after
            else:
                before, rest = original.split('def deflate_slow (', 1)
                before += 'def deflate_slow ('
                body, after = rest.split('/-- `local block_state deflate_rle(', 1)
                after = '/-- `local block_state deflate_rle(' + after
            if body.count(old) != 1:
                raise RuntimeError('ambiguous source mutation: ' + label)
            (scratch / source).write_text(before + body.replace(old, new) + after)
            if scope == 'body':
                if originals[fragment].count(old) != 1:
                    raise RuntimeError('ambiguous synchronized mutation: ' + label)
                (scratch / fragment).write_text(originals[fragment].replace(old, new))
                require(build('ZlibF.Proof.«deflate.c.engine.slow-source»'),
                        label + ' complete synchronized source equality')
            else:
                require(build('ZlibF.Zlib.«deflate_strategies.c»'), label + ' source compilation')
            result = build(module)
            error = re.search(r'^error: ([^\n]+)', result.stdout, re.MULTILINE)
            hit = re.match(r'([^:]+):(\d+):', error.group(1)) if error else None
            expected = hit and any(
                hit.group(1) == path and start <= int(hit.group(2)) < end
                for path, start, end in (spans[p] for p in proofs))
            resource = any(word in result.stdout.lower() for word in
                           ('maximum recursion depth', 'maximum number of heartbeats',
                            'deep recursion detected', 'deterministic timeout', 'interrupted', 'out of memory'))
            if result.returncode == 0 or not expected or resource:
                raise RuntimeError(label + ' survived or failed inconclusively:\n' + result.stdout)
            print('KILLED ' + label + ': ' + error.group(1), flush=True)


if __name__ == '__main__':
    main()
