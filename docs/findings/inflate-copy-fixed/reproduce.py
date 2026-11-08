#!/usr/bin/env python3
"""Compile unmodified decoder sources and require the pointer-pair diagnosis."""
from pathlib import Path
import os
import shlex
import subprocess
import tempfile


def main():
    finding = Path(__file__).resolve().parent
    root = finding.parents[2]
    source = root / 'zlib'
    compiler = shlex.split(os.environ.get('CC', 'clang'))
    units = ['adler32.c', 'crc32.c', 'inffast.c', 'inflate.c', 'inftrees.c', 'zutil.c']
    with tempfile.TemporaryDirectory(prefix='inflate-copy-fixed-') as directory:
        executable = Path(directory) / 'repro'
        command = compiler + [
            '-O1', '-g', '-fsanitize=address,pointer-compare,pointer-subtract',
            '-fno-omit-frame-pointer', '-I', str(source), str(finding / 'repro.c'),
        ] + [str(source / unit) for unit in units] + ['-o', str(executable)]
        subprocess.run(command, check=True)
        env = os.environ.copy()
        options = env.get('ASAN_OPTIONS', '')
        env['ASAN_OPTIONS'] = options + ':detect_invalid_pointer_pairs=2:detect_leaks=0'
        result = subprocess.run([str(executable)], env=env, text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        print(result.stdout, end='')
        required = ['inflate=0 produced=1 fixed_block=1',
                    'AddressSanitizer: invalid-pointer-pair', 'inflateCopy', 'lenfix']
        if result.returncode == 0 or not all(text in result.stdout for text in required):
            raise SystemExit('Expected inflateCopy pointer-pair diagnosis was not observed')
        print('CONFIRMED: default-init fixed-block inflateCopy compares unrelated objects')


if __name__ == '__main__':
    main()
