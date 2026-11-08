#!/usr/bin/env python3
"""Reject unsafe hint-detector mutations while full source equality still checks.

The accepted property is termination, read bounds, unchanged heap and the
binary/text return domain. Exact hint classification is a separate property.
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
    proof = Path('ZlibF/Proof/trees.c.detect.lean')
    originals = {p: (root / p).read_text() for p in (source, proof)}
    cases = (
        ('black-return-domain', 'black', 'return (n, bm, some Z_BINARY)',
         'return (n, bm, some Z_UNKNOWN)', 'data_type_black_safe'),
        ('text-return-domain', 'text', 'return (n, some Z_TEXT)',
         'return (n, some Z_UNKNOWN)', 'data_type_text_safe'),
        ('black-stalled-counter', 'black', 'iadd n 1', 'iadd n 0', 'data_type_black_safe'),
        ('text-stalled-counter', 'text', 'iadd n 1', 'iadd n 0', 'data_type_text_safe'),
        ('whitespace-return-domain', 'white', '    return Z_TEXT',
         '    return Z_UNKNOWN', 'detect_data_type_safe'),
        ('whitespace-read-bound', 'white', 'getFc (← pLtree s) 9',
         'getFc (← pLtree s) 600', 'detect_data_type_safe'),
    )
    selected = set(sys.argv[1:])
    if selected:
        unknown = selected - {x[0] for x in cases}
        if unknown:
            raise RuntimeError('unknown mutation labels: ' + ', '.join(sorted(unknown)))
        cases = tuple(x for x in cases if x[0] in selected)

    def replace_scoped(text, first, last, old, new, label):
        before, body = text.split(first, 1)
        body, after = body.split(last, 1)
        if body.count(old) != 1:
            raise RuntimeError('ambiguous source mutation: ' + label)
        return before + first + body.replace(old, new) + last + after

    with tempfile.TemporaryDirectory(prefix='trees-detect-') as directory:
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

        target = 'ZlibF.Proof.«deflate.c.engine.block-prepare»'
        require(build(target), 'positive complete preparation baseline')
        print('baseline: real detector, stream hint and all three constructors', flush=True)
        for label, scope, old, new, theorem in cases:
            before, body = originals[source].split('def detect_data_type (', 1)
            body, after = body.split('/-- `void ZLIB_INTERNAL _tr_flush_block', 1)
            white_marker = '  -- if (dyn_ltree[9]'
            text_marker = '  -- for (n = 32;'
            if scope == 'black':
                left, part = '', body.split(white_marker, 1)[0]
                right = white_marker + body.split(white_marker, 1)[1]
            elif scope == 'white':
                left, part = body.split(white_marker, 1)
                left += white_marker
                part, right = part.split(text_marker, 1)
                right = text_marker + right
            else:
                left, part = body.split(text_marker, 1)
                left += text_marker
                right = ''
            if part.count(old) != 1:
                raise RuntimeError('ambiguous actual mutation: ' + label)
            (scratch / source).write_text(before + 'def detect_data_type (' + left + part.replace(old, new)
                                          + right + '/-- `void ZLIB_INTERNAL _tr_flush_block' + after)
            first, last = {
                'black': ('def dataTypeBlack (', 'def dataTypeText ('),
                'text': ('def dataTypeText (', '/-- The complete source'),
                'white': ('theorem detect_data_type_source (', '/-- A literal-frequency'),
            }[scope]
            changed = replace_scoped(originals[proof], first, last, old, new, label)
            start_offset = changed.index('theorem ' + theorem)
            following = changed.find('\ntheorem ', start_offset + len('theorem ' + theorem))
            start = changed[:start_offset].count('\n') + 1
            end = len(changed.splitlines()) + 1 if following < 0 else changed[:following].count('\n') + 1
            require(build('ZlibF.Zlib.«trees.c»'), label + ' actual source compilation')
            cut = changed.split('/-- A literal-frequency', 1)[0]
            (scratch / proof).write_text(cut + '\nend Zlib.Trees.Proofs\n')
            require(build('ZlibF.Proof.«trees.c.detect»'), label + ' complete source equality')
            (scratch / proof).write_text(changed)
            # A rejection in the actual detector module prevents every
            # caller from checking. The complete caller baseline is checked
            # above; unrelated tree constructors need not replay per mutant.
            result = build('ZlibF.Proof.«trees.c.detect»')
            error = re.search(r'^error: ([^\n]+)', result.stdout, re.MULTILINE)
            hit = re.match(re.escape(str(proof)) + r':(\d+):', error.group(1)) if error else None
            resource = any(word in result.stdout.lower() for word in (
                'maximum recursion depth', 'maximum number of heartbeats', 'deep recursion detected',
                'deterministic timeout', 'interrupted', 'out of memory'))
            if result.returncode == 0 or hit is None or resource or not start <= int(hit.group(1)) < end:
                raise RuntimeError(label + ' survived or failed inconclusively:\n' + result.stdout)
            print('KILLED ' + label + ': ' + error.group(1) + '; full source equality checks', flush=True)


if __name__ == '__main__':
    main()
