#!/usr/bin/env python3
"""Reject actual public deflate pending-drain regressions.

The exact source cut points are synchronized first. Their whole-function
equality must check. A rejection counts only in the affected execution
proof; resource failures are inconclusive.
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
    originals = {path: (root / path).read_text() for path in (source, cut)}
    cases = (
        ('pending-output-check', 'entry',
         'if (← zrd strm (·.avail_out)) == 0 then',
         'if (← zrd strm (·.avail_out)) != 0 then',
         'public-pending', 'public_pending_exhausted_allowed'),
        ('pending-return', 'entry',
         'wr s (fun d => { d with last_flush := -1 })\n      return Z_OK',
         'wr s (fun d => { d with last_flush := -1 })\n      return Z_BUF_ERROR',
         'public-pending', 'public_pending_exhausted_allowed'),
        ('pending-retry-marker', 'entry',
         'wr s (fun d => { d with last_flush := -1 })',
         'wr s (fun d => { d with last_flush := 0 })',
         'public-pending', 'public_pending_exhausted_allowed'),
    )
    selection = set(sys.argv[1:])
    if selection:
        unknown = selection - {case[0] for case in cases}
        if unknown:
            raise RuntimeError('unknown mutation labels: ' + ', '.join(sorted(unknown)))
        cases = tuple(case for case in cases if case[0] in selection)
    spans = {}
    for _, _, _, _, proof, theorem in cases:
        path = Path('ZlibF/Proof/deflate.c.engine.' + proof + '.lean')
        text = (root / path).read_text()
        anchor = 'theorem ' + theorem
        start = text[:text.index(anchor)].count('\n') + 1
        following = text.find('\ntheorem ', text.index(anchor) + len(anchor))
        end = len(text.splitlines()) + 1 if following < 0 else text[:following].count('\n') + 1
        spans[(proof, theorem)] = (str(path), start, end)
    with tempfile.TemporaryDirectory(prefix='deflate-public-pending-') as directory:
        scratch = Path(directory)
        for name in ('lakefile.toml', 'lean-toolchain'):
            shutil.copy2(root / name, scratch / name)
        shutil.copytree(root / 'ZlibF', scratch / 'ZlibF')
        shutil.copytree(root / '.lake/build', scratch / '.lake/build')

        def build(target):
            return subprocess.run([lake, 'build', target], cwd=scratch,
                                  env=dict(os.environ, LC_ALL='C'), text=True,
                                  stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=600)

        def require(result, label):
            if result.returncode:
                raise RuntimeError(label + ':\n' + result.stdout)

        caller = os.environ.get('ZLIBF_PUBLIC_PENDING_CALLER', 'deflate.c.engine.public-pending')
        module = 'ZlibF.Proof.«' + caller + '»'
        require(build(module), 'positive actual public pending-drain baseline')
        print('baseline: actual public pending drain, all accepted flush flags, exact output and preserved retry state', flush=True)
        for label, scope, old, new, proof, theorem in cases:
            original = originals[source]
            before, body = original.split('def deflate (strm : ZStreamPtr)', 1)
            body, after = body.split('/-- `int ZEXPORT deflateParams(', 1)
            entry, rest = body.split('  -- Write the header\n', 1)
            header, tail = rest.split('  -- #ifdef GZIP\n', 1)
            parts = {'entry': entry, 'header': header, 'tail': tail}
            if parts[scope].count(old) != 1:
                raise RuntimeError('ambiguous source mutation: ' + label)
            parts[scope] = parts[scope].replace(old, new)
            (scratch / source).write_text(before + 'def deflate (strm : ZStreamPtr)' + parts['entry']
                + '  -- Write the header\n' + parts['header'] + '  -- #ifdef GZIP\n' + parts['tail']
                + '/-- `int ZEXPORT deflateParams(' + after)
            helper = originals[cut]
            if scope == 'tail':
                left, rest = helper.split('def publicDataTail (', 1)
                middle, right = rest.split('def publicZlibHeader (', 1)
                left += 'def publicDataTail ('
                right = 'def publicZlibHeader (' + right
            elif scope == 'header':
                left, rest = helper.split('def publicZlibHeader (', 1)
                middle, right = rest.split('set_option maxHeartbeats', 1)
                left += 'def publicZlibHeader ('
                right = 'set_option maxHeartbeats' + right
            else:
                left, middle = helper.split('theorem public_deflate_source (', 1)
                left += 'theorem public_deflate_source ('
                right = ''
            if middle.count(old) != 1:
                raise RuntimeError('ambiguous synchronized cut: ' + label)
            (scratch / cut).write_text(left + middle.replace(old, new) + right)
            require(build('ZlibF.Zlib.«deflate.c»'), label + ' source compilation')
            require(build('ZlibF.Proof.«deflate.c.engine.public-source»'), label + ' complete source equality')
            result = build(module)
            error = re.search(r'^error: ([^\n]+)', result.stdout, re.MULTILINE)
            path, start, end = spans[(proof, theorem)]
            hit = re.match(re.escape(path) + r':(\d+):', error.group(1)) if error else None
            resource = any(word in result.stdout.lower() for word in (
                'maximum recursion depth', 'maximum number of heartbeats', 'deep recursion detected',
                'deterministic timeout', 'interrupted', 'out of memory'))
            if result.returncode == 0 or hit is None or resource or not start <= int(hit.group(1)) < end:
                raise RuntimeError(label + ' survived or failed inconclusively:\n' + result.stdout)
            print('KILLED ' + label + ': ' + error.group(1), flush=True)


if __name__ == '__main__':
    main()
