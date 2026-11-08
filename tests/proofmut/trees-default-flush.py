#!/usr/bin/env python3
"""The full branch-independent default flush is the positive caller for real regressions."""
from pathlib import Path
import os
import subprocess
import sys


def main():
    directory = Path(__file__).resolve().parent
    env = os.environ.copy()
    env['ZLIBF_DYNAMIC_FLUSH_CALLER'] = 'deflate.c.engine.flush-default-output'
    env['ZLIBF_BLOCK_CALLER'] = 'ZlibF.Proof.«deflate.c.engine.flush-default-output»'
    subprocess.run([sys.executable, str(directory / 'trees-dynamic-flush.py')], env=env, check=True)
    subprocess.run([sys.executable, str(directory / 'deflate-block-output.py'),
                    'skip-bit-publication', 'pending-cursor-reset'], env=env, check=True)


if __name__ == '__main__':
    main()
