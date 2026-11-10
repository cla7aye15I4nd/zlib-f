#!/usr/bin/env python3
"""Check the actual public-view COPY boundary with synchronized source cuts.

Older raw-only copy execution proofs are omitted only in the temporary
baseline so rejection belongs to the new generic execution proof. They are
not replaced by assumptions, and the checkout remains unchanged.
"""
from pathlib import Path
import os
import re
import shutil
import subprocess
import tempfile


def main():
    root = Path(__file__).resolve().parents[2]
    source = Path('ZlibF/Zlib/inflate.c.lean')
    cut = Path('ZlibF/Proof/inflate.c.main.stored.lean')
    proof = Path('ZlibF/Proof/inflate.c.stored-views.lean')
    original = (root / source).read_text()
    literal = (root / cut).read_text()
    variants = (
        ('dropped-copy', 'memcpyB l.put l.next copy.toNat', 'memcpyB l.put l.next 0', 'memcpyB l.put l.next n.toNat', 'memcpyB l.put l.next 0'),
        ('wrong-input-advance', 'l.next.add (copy.toNat : Int)', 'l.next.add ((copy.toNat : Int) + 1)',
            'l.next.add (n.toNat : Int)', 'l.next.add ((n.toNat : Int) + 1)'),
        ('missing-output-accounting', 'left := l.left - copy', 'left := l.left', 'left := l.left - n', 'left := l.left'),
        ('missing-residual-decrease', 'length := s.length - copy', 'length := s.length', 'length := s.length - n', 'length := s.length'),
    )
    env = os.environ.copy()
    env['LC_ALL'] = 'C'
    target = 'ZlibF.Proof.«inflate.c.stored-default-state»'

    def build(where):
        return subprocess.run(['lake', 'build', target], cwd=where, env=env, text=True,
                              stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=600)

    with tempfile.TemporaryDirectory(prefix='inflate-stored-views-') as directory:
        scratch = Path(directory)
        for file in ('lakefile.toml', 'lean-toolchain'):
            shutil.copy2(root / file, scratch / file)
        shutil.copytree(root / 'ZlibF', scratch / 'ZlibF')
        shutil.copytree(root / '.lake', scratch / '.lake', ignore=shutil.ignore_patterns('*.tmp.*', 'Index.*'))
        stored = scratch / 'ZlibF/Proof/inflate.c.stored-call.lean'
        text = stored.read_text()
        a = text.rindex('/--', 0, text.index('theorem inflate_leave_raw_finish_done'))
        b = text.rindex('/--', 0, text.index('theorem LOAD_run'))
        c = text.rindex('/--', 0, text.index('theorem inflate_run_raw_copy'))
        stored.write_text(text[:a] + text[b:c] + '\nend Zlib.Inflate.Proofs\n')
        old = scratch / 'ZlibF/Proof/inflate.c.main.stored2.lean'
        text = old.read_text()
        a = text.rindex('/--', 0, text.index('theorem copyTail_run'))
        b = text.rindex('/--', 0, text.index('theorem inflate_COPY_leave'))
        old.write_text(text[:a] + text[b:])
        baseline = build(scratch)
        if baseline.returncode:
            raise RuntimeError('baseline failed:\n' + baseline.stdout)
        print('baseline: complete public-view COPY/COPY_ boundaries check', flush=True)
        for label, old, new, old_cut, new_cut in variants:
            a = original.index('def inflate_COPY (')
            b = original.index('def inflate_COPY_ (', a)
            section = original[a:b]
            if section.count(old) != 1:
                raise RuntimeError('ambiguous COPY mutation: ' + label)
            (scratch / source).write_text(original[:a] + section.replace(old, new) + original[b:])
            a = literal.index('def copyTail (')
            b = literal.index('theorem inflate_COPY_split', a)
            section = literal[a:b]
            if section.count(old_cut) != 1:
                raise RuntimeError('ambiguous literal COPY mutation: ' + label)
            (scratch / cut).write_text(literal[:a] + section.replace(old_cut, new_cut) + literal[b:])
            result = build(scratch)
            first = re.search(r'^error: ([^\n]+)', result.stdout, re.MULTILINE)
            hit = re.match(re.escape(str(proof)) + r':(\d+):', first.group(1)) if first else None
            text = (root / proof).read_text()
            begin = text.index('theorem copyTail_views_run ')
            end = text.index('theorem inflate_COPY_views_run ', begin)
            low, high = text[:begin].count('\n') + 1, text[:end].count('\n')
            exhausted = any(word in result.stdout.lower() for word in (
                'maximum recursion depth', 'maximum number of heartbeats', 'deterministic timeout'))
            if result.returncode == 0 or hit is None or not low <= int(hit.group(1)) <= high or exhausted:
                raise RuntimeError(label + ' lacks a direct non-resource proof failure:\n' + result.stdout)
            print('KILLED ' + label + ': ' + first.group(1), flush=True)
        print('PASS: four actual stored-copy mutants; no resource failures', flush=True)


if __name__ == '__main__':
    main()
