#!/usr/bin/env python3
"""Recheck actual repair/original-frequency mutants at the dynamic-budget caller."""
from pathlib import Path
import os
import subprocess
import sys


def main():
    directory = Path(__file__).resolve().parent
    env = os.environ.copy()
    env['ZLIBF_TREE_CALLER'] = 'ZlibF.Proof.«deflate.c.engine.dynamic-budget»'
    for script in ('trees-fib-origins.py', 'trees-bitlen-trace.py'):
        subprocess.run([sys.executable, str(directory / script)], env=env, check=True)


if __name__ == '__main__':
    main()
