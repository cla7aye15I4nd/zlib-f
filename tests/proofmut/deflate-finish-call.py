#!/usr/bin/env python3
"""Complete FINISH caller rejects actual wrong-return and skipped-loop code."""
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
    prefix = Path('ZlibF/Proof/deflate.c.engine.eof-insert.lean')
    tail = Path('ZlibF/Proof/deflate.c.engine.eof-tail.lean')
    originals = {p: (root / p).read_text() for p in (source, prefix, tail)}
    cases = (
        ('wrong-early-result', 'if let some r := st.ret then return r',
         'if let some _ := st.ret then return block_done'),
        ('bypassed-finish-loop', 'let st ← cwhile forever (deflate_slow_body s flush) {}',
         'let st : LoopS := { ret := some need_more }'),
    )
    proofs = (('slow-refill', 'slow_short_no_flush_boundary'),
              ('content-refill', 'slow_short_content_boundary'),
              ('slow-loop', 'deflate_slow_no_flush_before_block'),
              ('strategy-no-flush-loop', 'deflate_slow_no_flush_full'),
              ('strategy-finish', 'deflate_slow_finish_full'))
    spans = []
    for name, theorem in proofs:
        p = Path('ZlibF/Proof/deflate.c.engine.' + name + '.lean')
        text = (root / p).read_text()
        marker = text.index('theorem ' + theorem)
        end = text.find('\ntheorem ', marker + 1)
        spans.append((str(p), text[:marker].count('\n') + 1,
                      len(text.splitlines()) + 1 if end < 0 else text[:end].count('\n') + 1))
    env = dict(os.environ, LC_ALL='C')
    target = 'ZlibF.Proof.«deflate.c.engine.strategy-finish»'
    with tempfile.TemporaryDirectory(prefix='deflate-finish-call-') as directory:
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

        require(build(target), 'positive complete actual FINISH call')
        print('baseline: complete FINISH loop, EOF tail, return classification and accounting check', flush=True)
        for label, old, new in cases:
            left, rest = originals[source].split('def deflate_slow (', 1)
            body, right = rest.split('/-! ## `deflate_rle` -/', 1)
            if body.count(old) != 1:
                raise RuntimeError('ambiguous actual function mutation')
            (scratch / source).write_text(left + 'def deflate_slow (' + body.replace(old, new)
                                          + '/-! ## `deflate_rle` -/' + right)
            for p, start, end in ((prefix, 'theorem deflate_slow_eof_source', 'theorem eof_insert_count'),
                                  (tail, 'theorem deflate_slow_eof_tail_source', 'theorem slow_eof_finish_tail')):
                before, rest = originals[p].split(start, 1)
                declaration, after = rest.split(end, 1)
                if declaration.count(old) != 1:
                    raise RuntimeError('ambiguous synchronized source equality')
                (scratch / p).write_text(before + start + declaration.replace(old, new).replace('\n  rfl\n', '\n  try rfl\n') + end + after)
            # Independent whole-function source equality gate, with no older
            # whole-function execution theorem required to survive the mutant.
            first = (scratch / prefix).read_text()
            first = first[first.index('def eofInsert'):first.index('theorem eof_insert_count')]
            second = (scratch / tail).read_text()
            second = second[second.index('def slowEofTail'):second.index('/-- At actual EOF')]
            gate = ('import ZlibF.Proof.«deflate.c.engine.slow-source»\n'
                    'namespace Zlib.Deflate.Engine.Proofs\n'
                    'open C Zlib.Deflate Zlib.Deflate.Spec\nset_option autoImplicit false\n')
            (scratch / 'ZlibF/Proof/deflate.c.engine.finish-call-source-gate.lean').write_text(
                gate + first + second + '\nend Zlib.Deflate.Engine.Proofs\n')
            require(build('ZlibF.Proof.«deflate.c.engine.finish-call-source-gate»'),
                    label + ' actual function compilation and complete source equalities')
            result = build(target)
            error = re.search(r'^error: ([^\n]+)', result.stdout, re.MULTILINE)
            hit = re.match(r'([^:]+):(\d+):', error.group(1)) if error else None
            expected = hit and any(hit.group(1) == p and start <= int(hit.group(2)) < end
                                   for p, start, end in spans)
            resource = any(word in result.stdout.lower() for word in
                           ('maximum recursion depth', 'maximum number of heartbeats',
                            'deep recursion detected', 'deterministic timeout', 'interrupted', 'out of memory'))
            if result.returncode == 0 or not expected or resource:
                raise RuntimeError(label + ' survived or failed inconclusively:\n' + result.stdout)
            print('KILLED ' + label + ': ' + error.group(1)
                  + '; complete function source equalities check; no resource failure', flush=True)


if __name__ == '__main__':
    main()
