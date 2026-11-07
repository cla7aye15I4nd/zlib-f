#!/usr/bin/env python3
"""Reject real deferred-insertion mutants after source equalities check."""
from pathlib import Path
import os
import re
import shutil
import subprocess
import tempfile


def main():
    root = Path(__file__).resolve().parents[2]
    lake = shutil.which('lake') or str(Path.home() / '.elan/bin/lake')
    source = Path('ZlibF/Zlib/deflate_base.c.lean')
    whole = Path('ZlibF/Proof/deflate.c.engine.fill-source.lean')
    pending = Path('ZlibF/Proof/deflate.c.engine.fill-insert-source.lean')
    originals = {p: (root / p).read_text() for p in (source, whole, pending)}
    cases = (
        ('pending-counter',
         'wr s (fun d => { d with insert := d.insert - 1 })',
         'wr s (fun d => { d with insert := d.insert })',
         'wr s (fun d => { d with insert := d.insert - 1 })',
         'wr s (fun d => { d with insert := d.insert })', 'fill-insert-step', 'fill_insert_step'),
        ('pending-cursor', 'let str := str + 1', 'let str := str + 2',
         'let str := cursor.1 + 1', 'let str := cursor.1 + 2', 'fill-insert-step', 'fill_insert_step'),
        ('pending-break', 'pure (str, d.lookahead + d.insert < MIN_MATCH_u)',
         'pure (str, d.lookahead + d.insert ≤ MIN_MATCH_u)',
         'pure (str, d.lookahead + d.insert < MIN_MATCH_u)',
         'pure (str, d.lookahead + d.insert ≤ MIN_MATCH_u)', 'fill-insert-step', 'fill_insert_step'),
        ('pending-ignore-break', 'pure (ins != 0 && !brk, (str, brk))',
         'pure (ins != 0, (str, brk))', 'pure (ins != 0 && !cursor.2, cursor)',
         'pure (ins != 0, cursor)', 'fill-insert-loop', 'fill_insert_loop'),
        ('pending-seed-position', 'let str : UInt32 := d.strstart - d.insert',
         'let str : UInt32 := d.strstart', 'let str := d.strstart - d.insert',
         'let str := d.strstart', 'fill-prime-pending', 'fill_prime_pending'),
        ('pending-entry-guard', 'if d.lookahead + d.insert ≥ MIN_MATCH_u then',
         'if d.lookahead ≥ MIN_MATCH_u then', 'if d.lookahead + d.insert ≥ MIN_MATCH_u then',
         'if d.lookahead ≥ MIN_MATCH_u then', 'fill-prime-pending', 'fill_prime_pending'),
    )
    with tempfile.TemporaryDirectory(prefix='deflate-pending-insert-') as directory:
        scratch = Path(directory)
        for name in ('lakefile.toml', 'lean-toolchain'):
            shutil.copy2(root / name, scratch / name)
        shutil.copytree(root / 'ZlibF', scratch / 'ZlibF')
        shutil.copytree(root / '.lake/build', scratch / '.lake/build')

        def build(module):
            return subprocess.run([lake, 'build', 'ZlibF.Proof.«deflate.c.engine.' + module + '»'],
                                  cwd=scratch, env=dict(os.environ, LC_ALL='C'), text=True,
                                  stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=240)

        def require(result, label):
            if result.returncode:
                raise RuntimeError(label + ':\n' + result.stdout)

        require(build('fill-caller-storage'), 'positive actual refill, decoded content and resumed caller buffers')
        print('baseline: actual pending refill retains decoded content and caller buffers', flush=True)
        for label, old, new, part_old, part_new, module, theorem in cases:
            before, body = originals[source].split('def fill_window (', 1)
            body, after = body.split('/-! ## `putShortMSB`, `flush_pending` -/', 1)
            if (body.count(old) != 1 or originals[whole].count(old) != 1
                    or originals[pending].count(part_old) != 1):
                raise RuntimeError('ambiguous synchronized mutation: ' + label)
            (scratch / source).write_text(before + 'def fill_window (' + body.replace(old, new)
                                          + '/-! ## `putShortMSB`, `flush_pending` -/' + after)
            (scratch / whole).write_text(originals[whole].replace(old, new))
            (scratch / pending).write_text(originals[pending].replace(part_old, part_new))
            require(build('fill-insert-source'), label + ' complete source equalities and seed execution')
            result = build(module)
            proof = Path('ZlibF/Proof/deflate.c.engine.' + module + '.lean')
            text = (root / proof).read_text()
            start = text[:text.index('theorem ' + theorem)].count('\n') + 1
            following = text.find('\ntheorem ', text.index('theorem ' + theorem) + len(theorem))
            end = len(text.splitlines()) + 1 if following < 0 else text[:following].count('\n') + 1
            error = re.search(r'^error: ([^\n]+)', result.stdout, re.MULTILINE)
            hit = re.match(re.escape(str(proof)) + r':(\d+):', error.group(1)) if error else None
            resource = any(term in result.stdout.lower() for term in (
                'maximum recursion depth', 'maximum number of heartbeats', 'deep recursion detected',
                'deterministic timeout', 'interrupted', 'out of memory'))
            if (result.returncode == 0 or hit is None or resource
                    or not start <= int(hit.group(1)) < end):
                raise RuntimeError(label + ' survived or failed inconclusively:\n' + result.stdout)
            print('KILLED ' + label + ': ' + error.group(1), flush=True)


if __name__ == '__main__':
    main()
