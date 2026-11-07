#!/usr/bin/env python3
"""Reject actual slow-search and inline-literal-tally mutations.

Search mutations also change their named source fragment. The complete
slow-body source equality must still check before execution is rejected.
Resource failures and errors outside the designated proof are inconclusive.
"""
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
    source = Path('ZlibF/Zlib/deflate_strategies.c.lean')
    fragment = Path('ZlibF/Proof/deflate.c.engine.slow-source.lean')
    base = Path('ZlibF/Zlib/deflate_base.c.lean')
    originals = {p: (root / p).read_text() for p in (source, fragment, base)}
    search_module = 'ZlibF.Proof.«deflate.c.engine.slow-search»'
    tally_module = 'ZlibF.Proof.«deflate.c.engine.tally-literal»'
    threshold_module = 'ZlibF.Proof.«deflate.c.engine.slow-threshold»'
    cases = (
        ('nil-candidate', source,
         'if hash_head != 0 && d.prev_length < d.max_lazy_match &&',
         'if true && d.prev_length < d.max_lazy_match &&',
         'deflate.c.engine.slow-find', 'theorem slow_find_evidence'),
        ('short-match-filter', source,
         'wr s (fun d => { d with match_length := MIN_MATCH_u - 1 })',
         'wr s (fun d => { d with match_length := MIN_MATCH_u })',
         'deflate.c.engine.slow-find', 'theorem slow_find_evidence'),
        ('deferred-byte-flag', source,
         'wr s (fun d => { d with match_available := 1, strstart := d.strstart + 1, lookahead := d.lookahead - 1 })',
         'wr s (fun d => { d with match_available := 0, strstart := d.strstart + 1, lookahead := d.lookahead - 1 })',
         'deflate.c.engine.slow-defer', 'theorem slow_defer_run'),
        ('deferred-byte-count', source,
         'wr s (fun d => { d with match_available := 1, strstart := d.strstart + 1, lookahead := d.lookahead - 1 })',
         'wr s (fun d => { d with match_available := 1, strstart := d.strstart + 1, lookahead := d.lookahead - 2 })',
         'deflate.c.engine.slow-defer', 'theorem slow_defer_run'),
        ('literal-byte-offset', base,
         'store_at d.sym_buf (d.sym_next + 2).toNat cc',
         'store_at d.sym_buf (d.sym_next + 1).toNat cc',
         'deflate.c.engine.tally-literal', 'theorem tally_literal_run'),
        ('literal-frequency-index', base,
         'freq_inc (.dstate_dyn_ltree id) cc.toNat',
         'freq_inc (.dstate_dyn_ltree id) 0',
         'deflate.c.engine.tally-literal', 'theorem tally_literal_run'),
    )
    proof_texts = {proof: (root / ('ZlibF/Proof/' + proof + '.lean')).read_text()
                   for _, _, _, _, proof, _ in cases}
    with tempfile.TemporaryDirectory(prefix='deflate-search-tally-') as directory:
        scratch = Path(directory)
        for name in ('lakefile.toml', 'lean-toolchain'):
            shutil.copy2(root / name, scratch / name)
        shutil.copytree(root / 'ZlibF', scratch / 'ZlibF')
        shutil.copytree(root / '.lake/build', scratch / '.lake/build')

        def build(*modules):
            return subprocess.run([lake, 'build', *modules], cwd=scratch, env=env,
                                  text=True, stdout=subprocess.PIPE,
                                  stderr=subprocess.STDOUT, timeout=180)

        def require(result, label):
            if result.returncode:
                raise RuntimeError(label + ':\n' + result.stdout)

        require(build(search_module, tally_module, threshold_module), 'positive combined proof baseline')
        print('baseline: actual search, deferred-byte call and inline-tally proofs check', flush=True)
        for label, path, old, new, proof, theorem in cases:
            for p, original in originals.items():
                (scratch / p).write_text(original)
            original = originals[path]
            if path == source:
                before, rest = original.split('def deflate_slow_body (', 1)
                body, after = rest.split('/-- `local block_state deflate_slow(', 1)
                if body.count(old) != 1 or originals[fragment].count(old) != 1:
                    raise RuntimeError('ambiguous synchronized mutation: ' + label)
                (scratch / path).write_text(before + 'def deflate_slow_body (' + body.replace(old, new)
                                            + '/-- `local block_state deflate_slow(' + after)
                (scratch / fragment).write_text(originals[fragment].replace(old, new))
                require(build('ZlibF.Proof.«deflate.c.engine.slow-source»'),
                        label + ' complete synchronized source equality')
                target = threshold_module if proof.endswith('slow-defer') else search_module
            else:
                if original.count(old) != 1:
                    raise RuntimeError('ambiguous literal mutation: ' + label)
                (scratch / path).write_text(original.replace(old, new))
                require(build('ZlibF.Zlib.«deflate_base.c»'), label + ' source compilation')
                target = tally_module
            result = build(target)
            error = re.search(r'^error: ([^\n]+)', result.stdout, re.MULTILINE)
            expected = 'ZlibF/Proof/' + proof + '.lean'
            hit = re.match(re.escape(expected) + r':(\d+):', error.group(1)) if error else None
            text = proof_texts[proof]
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
