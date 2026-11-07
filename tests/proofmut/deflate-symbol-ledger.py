#!/usr/bin/env python3
"""Check semantic symbol packing and the signed sliding subtraction."""
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
    packing = Path('ZlibF/Proof/deflate.c.engine.tally-match.lean')
    ledger = Path('ZlibF/Proof/deflate.c.engine.symbol-ledger.lean')
    balance = Path('ZlibF/Proof/deflate.c.engine.block-balance.lean')
    original_source = (root / source).read_text()
    original_packing = (root / packing).read_text()
    with tempfile.TemporaryDirectory(prefix='deflate-symbol-ledger-') as directory:
        scratch = Path(directory)
        for name in ('lakefile.toml', 'lean-toolchain'):
            shutil.copy2(root / name, scratch / name)
        shutil.copytree(root / 'ZlibF', scratch / 'ZlibF')
        shutil.copytree(root / '.lake/build', scratch / '.lake/build')

        def run(module):
            return subprocess.run([lake, 'build', 'ZlibF.Proof.«' + module + '»'],
                                  cwd=scratch, env=dict(os.environ, LC_ALL='C'), text=True,
                                  stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=240)

        def require(result, label):
            if result.returncode:
                raise RuntimeError(label + ':\n' + result.stdout)

        def rejected(result, label, proof, theorem):
            error = re.search(r'^error: ([^\n]+)', result.stdout, re.MULTILINE)
            hit = re.match(re.escape(str(proof)) + r':(\d+):', error.group(1)) if error else None
            text = (root / proof).read_text()
            start = text[:text.index('theorem ' + theorem)].count('\n') + 1
            next_theorem = text.find('\ntheorem ', text.index('theorem ' + theorem) + 1)
            end = (len(text.splitlines()) + 1 if next_theorem < 0
                   else text[:next_theorem].count('\n') + 1)
            resource = any(term in result.stdout.lower() for term in (
                'maximum recursion depth', 'maximum number of heartbeats', 'deep recursion detected',
                'deterministic timeout', 'interrupted', 'out of memory'))
            if (result.returncode == 0 or hit is None or resource
                    or not start <= int(hit.group(1)) < end):
                raise RuntimeError(label + ' survived or failed inconclusively:\n' + result.stdout)
            print('KILLED ' + label + ': ' + error.group(1), flush=True)

        require(run('deflate.c.engine.block-balance'), 'positive initializer, ledger and balance baseline')
        print('baseline: actual initialization, both tallies and signed slide subtraction check', flush=True)

        before, rest = original_source.split('def tally_dist (', 1)
        body, after = rest.split('/-! ## `slide_hash`', 1)
        old = '(dist >>> 8).toUInt8'
        if body.count(old) != 1:
            raise RuntimeError('ambiguous packing mutation')
        (scratch / source).write_text(before + 'def tally_dist (' + body.replace(old, '(dist >>> 7).toUInt8')
                                      + '/-! ## `slide_hash`' + after)
        # Synchronize the execution result and its exact byte view. The old
        # safety/execution proofs must pass before testing the semantic ledger.
        (scratch / packing).write_text(original_packing.replace('>>> 8', '>>> 7'))
        require(run('deflate.c.engine.tally-match'), 'synchronized high-byte mutant execution')
        rejected(run('deflate.c.engine.symbol-ledger'), 'match-high-byte-semantics', ledger, 'ledger_match')

        for label, expression in (('slide-drop-subtraction', 'a.toInt'),
                                  ('slide-reverse-subtraction', 'b.toInt - a.toInt')):
            (scratch / packing).write_text(original_packing)
            old = 'def lsub (a b : Int64) : M Int64 := chk64 (a.toInt - b.toInt)'
            if original_source.count(old) != 1:
                raise RuntimeError('ambiguous signed subtraction mutation')
            (scratch / source).write_text(original_source.replace(old,
                'def lsub (a b : Int64) : M Int64 := chk64 (' + expression + ')'))
            require(run('deflate.c.engine.symbol-ledger'), label + ' independent initialization and ledger')
            rejected(run('deflate.c.engine.block-balance'), label, balance, 'block_start_slide_run')


if __name__ == '__main__':
    main()
