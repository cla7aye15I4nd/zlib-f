#!/usr/bin/env python3
"""Check actual publication regressions with the complete dynamic-output caller."""
from pathlib import Path
import os
import subprocess
import sys


def main():
    directory = Path(__file__).resolve().parent
    env = os.environ.copy()
    env['ZLIBF_BLOCK_CALLER'] = 'ZlibF.Proof.«deflate.c.engine.dynamic-block-output»'
    subprocess.run([sys.executable, str(directory / 'deflate-block-output.py'),
                    'skip-bit-publication', 'pending-cursor-reset'], env=env, check=True)


if __name__ == '__main__':
    main()
