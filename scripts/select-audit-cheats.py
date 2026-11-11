#!/usr/bin/env python3
"""Partition the complete immutable auditor-cheat inventory without omissions."""
import argparse
from pathlib import Path
import sys


def select(directory: Path, count: int, index: int) -> list[Path]:
    if count <= 0 or not 0 <= index < count:
        raise ValueError('shard count must be positive and index must be in range')
    cases = sorted(directory.glob('*.lean'))
    if not cases:
        raise ValueError('empty auditor-cheat inventory')
    if any(p.is_symlink() or not p.is_file() or '\n' in str(p) or '\r' in str(p) for p in cases):
        raise ValueError('cheat inventory must contain ordinary files with line-safe names')
    selected = [p for ordinal, p in enumerate(cases) if ordinal % count == index]
    if not selected:
        raise ValueError('empty auditor-cheat shard')
    return selected


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('directory', type=Path)
    parser.add_argument('count', type=int)
    parser.add_argument('index', type=int)
    args = parser.parse_args()
    try:
        for path in select(args.directory, args.count, args.index):
            print(path)
    except ValueError as error:
        print(str(error), file=sys.stderr)
        return 2
    return 0


if __name__ == '__main__':
    sys.exit(main())
