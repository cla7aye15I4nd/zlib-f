#!/usr/bin/env python3
"""Reject resumed-fill mutations after the whole source equality checks."""
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
    source = Path('ZlibF/Zlib/deflate_base.c.lean')
    fragment = Path('ZlibF/Proof/deflate.c.engine.fill-source.lean')
    originals = {p: (root / p).read_text() for p in (source, fragment)}
    cases = (
        ('resume-hash-position',
         'let str : UInt32 := d.strstart - d.insert', 'let str : UInt32 := 0',
         'fill-prime-resume', 'theorem fill_prime_resume'),
        ('resume-copy-position',
         'let dst ← padd (← padd d.window d.strstart.toNat) d.lookahead.toNat',
         'let dst ← padd d.window d.lookahead.toNat',
         'fill-read-resume', 'theorem fill_body_resume_read'),
        ('resume-lookahead-offset',
         'let dst ← padd (← padd d.window d.strstart.toNat) d.lookahead.toNat',
         'let dst ← padd (← padd d.window d.strstart.toNat) 0',
         'fill-read-resume', 'theorem fill_body_resume_read'),
        ('padding-start-offset',
         'memsetB (← padd d.window curr.toNat) 0 init.toUInt32.toNat',
         'memsetB (← padd d.window (curr.toNat + 1)) 0 init.toUInt32.toNat',
         'fill-high-water', 'theorem fill_high_water_complete'),
        ('padding-resume-count',
         'let mut init : UInt64 := curr + WIN_INIT_u - d.high_water',
         'let mut init : UInt64 := curr + WIN_INIT_u - d.high_water + 1',
         'fill-high-water', 'theorem fill_high_water_complete'),
        ('padding-mark',
         'wr s (fun d => { d with high_water := curr + init })',
         'wr s (fun d => { d with high_water := curr + init + 1 })',
         'fill-high-water', 'theorem fill_high_water_complete'),
    )
    proofs = {name: (root / f'ZlibF/Proof/deflate.c.engine.{name}.lean').read_text()
              for _, _, _, name, _ in cases}
    with tempfile.TemporaryDirectory(prefix='deflate-fill-resume-') as directory:
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

        require(build('ZlibF.Proof.«deflate.c.engine.fill-caller»'), 'positive complete caller boundary')
        print('baseline: actual resumed fill and caller boundary check', flush=True)
        for label, old, new, name, theorem in cases:
            before, body = originals[source].split('def fill_window (', 1)
            if body.count(old) != 1 or originals[fragment].count(old) != 1:
                raise RuntimeError('ambiguous synchronized mutation: ' + label)
            (scratch / source).write_text(before + 'def fill_window (' + body.replace(old, new))
            (scratch / fragment).write_text(originals[fragment].replace(old, new))
            require(build('ZlibF.Proof.«deflate.c.engine.fill-source»'), label + ' whole-source equality')
            result = build(f'ZlibF.Proof.«deflate.c.engine.{name}»')
            error = re.search(r'^error: ([^\n]+)', result.stdout, re.MULTILINE)
            expected = f'ZlibF/Proof/deflate.c.engine.{name}.lean'
            hit = re.match(re.escape(expected) + r':(\d+):', error.group(1)) if error else None
            text = proofs[name]
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
