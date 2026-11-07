#!/usr/bin/env python3
"""Check inline match-tally proofs against synchronized source mutations."""
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
    proof = Path('ZlibF/Proof/deflate.c.engine.tally-match.lean')
    original_source = (root / source).read_text()
    original_proof = (root / proof).read_text()
    module = 'ZlibF.Proof.«deflate.c.engine.tally-match»'
    cases = (
        ('match-distance-decrement',
         'let dist : UInt16 := dist - 1', 'let dist : UInt16 := dist',
         'let dist := dist - 1', 'let dist := dist', 'theorem match_tally_tail_run'),
        ('match-high-byte',
         '(dist >>> 8).toUInt8', '(dist >>> 7).toUInt8',
         '(distance.toUInt16 >>> 8).toUInt8', '(distance.toUInt16 >>> 7).toUInt8',
         'theorem tally_match_run'),
        ('match-distance-frequency',
         'freq_inc (.dstate_dyn_dtree id) dc.toNat', 'freq_inc (.dstate_dyn_dtree id) 0',
         'freq_inc (.dstate_dyn_dtree id) dc.toNat', 'freq_inc (.dstate_dyn_dtree id) 0',
         'theorem match_tally_tail_run'),
    )
    with tempfile.TemporaryDirectory(prefix='deflate-match-tally-') as directory:
        scratch = Path(directory)
        for name in ('lakefile.toml', 'lean-toolchain'):
            shutil.copy2(root / name, scratch / name)
        shutil.copytree(root / 'ZlibF', scratch / 'ZlibF')
        shutil.copytree(root / '.lake/build', scratch / '.lake/build')

        def run(*args):
            return subprocess.run([lake, *args], cwd=scratch, env=env, text=True,
                                  stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=180)

        def require(result, label):
            if result.returncode:
                raise RuntimeError(label + ':\n' + result.stdout)

        require(run('build', module), 'positive actual match-tally baseline')
        print('baseline: actual inline match tally checks', flush=True)
        for label, old, new, fragment_old, fragment_new, theorem in cases:
            before, rest = original_source.split('def tally_dist (', 1)
            body, after = rest.split('/-! ## `slide_hash`', 1)
            prefix, execution = original_proof.split('theorem match_tally_tail_run', 1)
            if body.count(old) != 1 or prefix.count(fragment_old) != 1:
                raise RuntimeError('ambiguous synchronized mutation: ' + label)
            (scratch / source).write_text(before + 'def tally_dist (' + body.replace(old, new)
                                          + '/-! ## `slide_hash`' + after)
            prefix = prefix.replace(fragment_old, fragment_new)
            (scratch / proof).write_text(prefix + 'theorem match_tally_tail_run' + execution)
            require(run('build', 'ZlibF.Proof.«deflate.c.engine.tally-distance»'),
                    label + ' translated source and independent helpers')
            sanity = scratch / '.lake/match-source-mutant.lean'
            sanity.write_text(prefix + '\nend Zlib.Deflate.Engine.Proofs\n')
            require(run('env', 'lean', str(sanity)), label + ' complete source equality')
            result = run('build', module)
            error = re.search(r'^error: ([^\n]+)', result.stdout, re.MULTILINE)
            hit = re.match(re.escape(str(proof)) + r':(\d+):', error.group(1)) if error else None
            start = original_proof[:original_proof.index(theorem)].count('\n') + 1
            following = original_proof.find('\ntheorem ', original_proof.index(theorem) + len(theorem))
            end = (len(original_proof.splitlines()) + 1 if following < 0
                   else original_proof[:following].count('\n') + 1)
            resource = any(word in result.stdout.lower() for word in
                           ('maximum recursion depth', 'maximum number of heartbeats',
                            'deep recursion detected', 'deterministic timeout', 'interrupted', 'out of memory'))
            if (result.returncode == 0 or hit is None or resource
                    or not start <= int(hit.group(1)) < end):
                raise RuntimeError(label + ' survived or failed inconclusively:\n' + result.stdout)
            print('KILLED ' + label + ': ' + error.group(1), flush=True)


if __name__ == '__main__':
    main()
