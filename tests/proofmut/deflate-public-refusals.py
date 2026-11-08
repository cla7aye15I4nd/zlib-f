#!/usr/bin/env python3
"""Actual public refusal guards fail their matching execution proofs.

The complete ordinary-request history is the positive caller. Mutations
synchronize the whole translated public function and its source equality.
A matching source-prefix execution failure is required; resource failures
are inconclusive. No production source is changed.
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
    source = Path('ZlibF/Zlib/deflate.c.lean')
    cut = Path('ZlibF/Proof/deflate.c.engine.public-source.lean')
    originals = {p: (root / p).read_text() for p in (source, cut)}
    new_input = ('if (← rd s (·.status)) == FINISH_STATE && (← zrd strm (·.avail_in)) != 0 then\n'
                 '    return ← ERR_RETURN strm Z_BUF_ERROR')
    cases = (
        ('null-output-guard', 'if z.next_out == .null || (z.avail_in != 0 && z.next_in == .null) ||',
         'if false || (z.avail_in != 0 && z.next_in == .null) ||',
         'public-entry-refusal-source', 'public_stream_guard_refusal'),
        ('null-input-guard', '(z.avail_in != 0 && z.next_in == .null)', 'false',
         'public-entry-refusal-source', 'public_stream_guard_refusal'),
        ('finished-other-flag-guard', '(d.status == FINISH_STATE && flush != Z_FINISH) then', 'false then',
         'public-entry-refusal-source', 'public_stream_guard_refusal'),
        ('zero-output-code', 'if z.avail_out == 0 then return ← ERR_RETURN strm Z_BUF_ERROR',
         'if z.avail_out == 0 then return ← ERR_RETURN strm Z_STREAM_ERROR',
         'public-entry-refusal-source', 'public_zero_output_refusal'),
        ('duplicate-request-check',
         'else if z.avail_in == 0 && (← RANK flush) ≤ (← RANK old_flush) && flush != Z_FINISH then',
         'else if false then', 'no-flush-duplicate-source', 'public_busy_no_flush_duplicate_source'),
        ('finished-new-input-code', new_input, new_input.replace('Z_BUF_ERROR', 'Z_STREAM_ERROR'),
         'finish-new-input-source', 'public_finished_new_input_source'),
        ('finished-new-input-drop', new_input, 'if false then\n    return ← ERR_RETURN strm Z_BUF_ERROR',
         'finish-new-input-source', 'public_finished_new_input_source'),
        ('upper-flush-guard',
         'if (← deflateStateCheck strm) != 0 || flush > Z_BLOCK || flush < 0 then',
         'if (← deflateStateCheck strm) != 0 || false || flush < 0 then',
         'public-entry-refusal-source', 'public_bad_flush_refusal'),
    )
    selection = set(sys.argv[1:])
    if selection:
        unknown = selection - {c[0] for c in cases}
        if unknown:
            raise RuntimeError('unknown mutation labels: ' + ', '.join(sorted(unknown)))
        cases = tuple(c for c in cases if c[0] in selection)
    env = dict(os.environ, LC_ALL='C')
    caller = os.environ.get('ZLIBF_PUBLIC_REFUSALS_CALLER', 'deflate.c.engine.ordinary-request-history')
    spans = {}
    for _, _, _, name, theorem in cases:
        path = Path('ZlibF/Proof/deflate.c.engine.' + name + '.lean')
        text = (root / path).read_text()
        marker = text.index('theorem ' + theorem)
        following = text.find('\ntheorem ', marker + 1)
        spans[(name, theorem)] = (str(path), text[:marker].count('\n') + 1,
                                  len(text.splitlines()) + 1 if following < 0 else text[:following].count('\n') + 1)
    with tempfile.TemporaryDirectory(prefix='deflate-public-refusals-') as directory:
        scratch = Path(directory)
        for name in ('lakefile.toml', 'lean-toolchain'):
            shutil.copy2(root / name, scratch / name)
        shutil.copytree(root / 'ZlibF', scratch / 'ZlibF')
        shutil.copytree(root / '.lake/build', scratch / '.lake/build')

        def build(module):
            return subprocess.run([lake, 'build', module], cwd=scratch, env=env, text=True,
                                  stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=600)

        def require(result, label):
            if result.returncode:
                raise RuntimeError(label + ':\n' + result.stdout)

        require(build('ZlibF.Proof.«' + caller + '»'), 'positive complete ordinary-request history')
        print('baseline: actual init, all ordinary requests, refusals and history preservation check', flush=True)
        for label, old, new, name, theorem in cases:
            for path, original in originals.items():
                first = 'def deflate (strm : ZStreamPtr)' if path == source else 'theorem public_deflate_source ('
                before, body = original.split(first, 1)
                if path == source:
                    body, after = body.split('/-- `int ZEXPORT deflateParams(', 1)
                    ending = '/-- `int ZEXPORT deflateParams(' + after
                else:
                    body, after = body.split('\nend Zlib.Deflate.Engine.Proofs', 1)
                    ending = '\nend Zlib.Deflate.Engine.Proofs' + after
                if body.count(old) != 1:
                    raise RuntimeError('ambiguous synchronized mutation: ' + label + ': ' + str(path))
                (scratch / path).write_text(before + first + body.replace(old, new) + ending)
            require(build('ZlibF.Zlib.«deflate.c»'), label + ' actual source compilation')
            require(build('ZlibF.Proof.«deflate.c.engine.public-source»'), label + ' complete public source equality')
            result = build('ZlibF.Proof.«deflate.c.engine.' + name + '»')
            error = re.search(r'^error: ([^\n]+)', result.stdout, re.MULTILINE)
            path, start, end = spans[(name, theorem)]
            hit = re.match(re.escape(path) + r':(\d+):', error.group(1)) if error else None
            resource = any(word in result.stdout.lower() for word in (
                'maximum recursion depth', 'maximum number of heartbeats', 'deep recursion detected',
                'deterministic timeout', 'interrupted', 'out of memory'))
            if result.returncode == 0 or hit is None or resource or not start <= int(hit.group(1)) < end:
                raise RuntimeError(label + ' survived or failed inconclusively:\n' + result.stdout)
            print('KILLED ' + label + ': ' + error.group(1)
                  + '; complete public source equality checks; no resource failure', flush=True)


if __name__ == '__main__':
    main()
