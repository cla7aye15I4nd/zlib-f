#!/usr/bin/env python3
"""Check actual fixed/stored/dynamic copies against C, including pointer sanitizers."""
from pathlib import Path
import os
import shlex
import subprocess
import zlib


def main():
    root = Path(__file__).resolve().parents[3]
    work = root / 'tests/build/inflate-copy'
    work.mkdir(parents=True, exist_ok=True)
    env = os.environ.copy()
    compiler = shlex.split(env.get('CC', 'clang'))

    def checked(command, name, cwd=root, input_text=None, environment=env):
        result = subprocess.run(command, cwd=cwd, env=environment, text=True,
                                input=input_text, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        (work / (name + '.out')).write_text(result.stdout)
        (work / (name + '.err')).write_text(result.stderr)
        if result.returncode:
            raise RuntimeError(name + ' failed:\n' + result.stdout[-4000:] + result.stderr[-4000:])
        return result

    def compress(payload, level=6, strategy=zlib.Z_DEFAULT_STRATEGY, wrapper=15):
        encoder = zlib.compressobj(level, zlib.DEFLATED, wrapper, 8, strategy)
        return encoder.compress(payload) + encoder.flush()

    fixed = b'A' * 128
    stored = bytes(range(64))
    dynamic = (b'a' * 100 + b'b' * 40 + b'c' * 20 + b'd' * 10 + b'efghijklmnop') * 2
    fixed_stream = compress(fixed, strategy=zlib.Z_FIXED)
    stored_stream = compress(stored, level=0)
    dynamic_stream = compress(dynamic, strategy=zlib.Z_HUFFMAN_ONLY)
    assert [(data[2] >> 1) & 3 for data in (fixed_stream, stored_stream, dynamic_stream)] == [1, 0, 2]
    cases = []
    for payload, data, chunks in (
            (fixed, fixed_stream, [(0, 1), (0, 7), (1, 1), (0, 32)]),
            (stored, stored_stream, [(0, 7), (1, 1)]),
            (dynamic, dynamic_stream, [(0, 7), (3, 11), (0, 64)])):
        for input_chunk, output_chunk in chunks:
            cases.append((15, input_chunk, output_chunk, data, payload))
    cases.append((-15, 0, 7, compress(fixed, strategy=zlib.Z_FIXED, wrapper=-15), fixed))
    cases.append((31, 0, 9, compress(fixed, strategy=zlib.Z_FIXED, wrapper=31), fixed))
    inputs = ''.join(f'inflate {wb} {inch} {outch} 0 2 hex: hex:{data.hex()}\n'
                     for wb, inch, outch, data, _ in cases)
    (work / 'cases.in').write_text(inputs)
    checked(['lake', 'build', 'difftest_inflate'], 'lean-build', cwd=root / 'tests')
    lean = checked([str(root / 'tests/.lake/build/bin/difftest_inflate')], 'lean', input_text=inputs)
    rows = lean.stdout.splitlines()
    if len(rows) != len(cases) or lean.stderr:
        raise RuntimeError('Lean output protocol is incomplete or has diagnostics')
    for row, (_, _, _, _, expected) in zip(rows, cases):
        if not row.startswith('init=0 rc=1 ') or 'c0;' not in row or not row.endswith(' out=' + expected.hex()):
            raise RuntimeError('Copy, completion or decompressed payload was not observed: ' + row[:500])

    for variant, flags in (
            ('plain', []),
            ('san', ['-fsanitize=address,undefined', '-fno-omit-frame-pointer']),
            ('ptr', ['-fsanitize=address,pointer-compare,pointer-subtract',
                     '-fno-omit-frame-pointer'])):
        library = work / ('zlib-' + variant)
        build_env = env.copy()
        build_env['CC'] = env.get('CC', 'clang')
        build_env['CFLAGS'] = ' '.join(['-O1', '-g'] + flags)
        checked(['bash', str(root / 'tests/build-zlib.sh'), str(root / 'zlib'), str(library)],
                'c-build-' + variant, environment=build_env)
        executable = work / ('inflate-' + variant)
        checked(compiler + ['-O1', '-g', '-Wall', '-Wextra'] + flags +
                ['-I', str(library), str(root / 'tests/c/inflate.c'), str(library / 'libz.a'),
                 '-o', str(executable)], 'driver-build-' + variant)
        run_env = env.copy()
        if variant != 'plain':
            run_env['ASAN_OPTIONS'] = 'detect_invalid_pointer_pairs=2:detect_leaks=0:halt_on_error=1'
            run_env['UBSAN_OPTIONS'] = 'halt_on_error=1'
        actual = checked([str(executable)], 'c-' + variant, input_text=inputs, environment=run_env)
        if actual.stderr or actual.stdout != lean.stdout:
            raise RuntimeError('C/Lean copy mismatch or sanitizer diagnostic: ' + variant)
        print(f'PASS: {len(cases)} actual C/Lean copy rows, complete payloads ({variant})', flush=True)


if __name__ == '__main__':
    main()
