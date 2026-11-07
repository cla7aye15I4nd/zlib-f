#!/usr/bin/env python3
"""Check source symbol mutations with the constructed default dynamic caller."""
from pathlib import Path
import os
import subprocess
import sys


def main():
    directory = Path(__file__).resolve().parent
    env = os.environ.copy()
    env['ZLIBF_PAYLOAD_CALLER'] = 'ZlibF.Proof.«deflate.c.engine.dynamic-prepared-payload»'
    env['ZLIBF_PAYLOAD_MUTATION_TARGET'] = 'ZlibF.Proof.«trees.c.compress-dynamic»'
    subprocess.run([sys.executable, str(directory / 'trees-compress-matches.py'),
                    'length-width', 'distance-decrement', 'length-code-index'], env=env, check=True)
    subprocess.run([sys.executable, str(directory / 'trees-compress-literals.py')], env=env, check=True)


if __name__ == '__main__':
    main()
