#!/usr/bin/env python3
"""Transport one build within one workflow run; never transport a test verdict.

Cross-run caches are only Lake inputs. The producer always asks Lake to validate
their traces against source. Consumers accept this run's exact checkout and
platform, then use Lake's --no-build check before the independent kernel audit.
"""
import argparse
import hashlib
import io
import json
from pathlib import Path, PurePosixPath
import platform
import subprocess
import tarfile

ROOT = Path(__file__).resolve().parents[1]
METADATA = 'build-manifest.json'
PREFIXES = ('.lake', 'tests/.lake')


def identity(root: Path) -> dict:
    tracked = subprocess.check_output(['git', 'ls-files', '-z'], cwd=root).decode().split('\0')
    names = sorted(name for name in tracked if name and (name.endswith('.lean') or
                   Path(name).name in {'lakefile.toml', 'lakefile.lean', 'lean-toolchain'}))
    inputs = {}
    for name in names:
        source = root / name
        if source.is_symlink() or not source.is_file():
            raise ValueError('build input is missing or symlinked: ' + name)
        inputs[name] = hashlib.sha256(source.read_bytes()).hexdigest()
    if not inputs:
        raise ValueError('empty compilation input set')
    return {'version': 1, 'commit': subprocess.check_output(
        ['git', 'rev-parse', 'HEAD'], cwd=root, text=True).strip(),
        'system': platform.system(), 'machine': platform.machine(),
        'compiler': subprocess.check_output(['cc', '--version'], text=True).strip(),
        'os_release': Path('/etc/os-release').read_text() if Path('/etc/os-release').is_file() else '',
        'inputs': inputs}


def validate_members(members: list[tarfile.TarInfo]) -> None:
    seen = set()
    for member in members:
        path = PurePosixPath(member.name)
        if member.name in seen or path.is_absolute() or '..' in path.parts:
            raise ValueError('unsafe or duplicate artifact member: ' + member.name)
        seen.add(member.name)
        if not (member.isfile() or member.isdir()):
            raise ValueError('links and special files are not build artifacts: ' + member.name)
        if member.name == METADATA:
            if not member.isfile():
                raise ValueError('build manifest must be a file')
        elif not any(member.name == prefix or member.name.startswith(prefix + '/') for prefix in PREFIXES):
            raise ValueError('artifact may contain only build outputs: ' + member.name)
    if METADATA not in seen:
        raise ValueError('missing build manifest')


def pack(root: Path, output: Path) -> None:
    metadata = json.dumps(identity(root), sort_keys=True).encode()
    if not (root / '.lake/build/lib/lean/ZlibF.olean').is_file():
        raise ValueError('full library build is missing')
    with tarfile.open(output, 'w:gz', compresslevel=1) as archive:
        record = tarfile.TarInfo(METADATA)
        record.size = len(metadata)
        archive.addfile(record, io.BytesIO(metadata))
        for prefix in PREFIXES:
            if (root / prefix).is_dir():
                # Tools link from their retained module/object outputs when
                # needed. Their large unused executables do not travel to every
                # consumer; differential driver executables remain included.
                archive.add(root / prefix, arcname=prefix, filter=lambda entry:
                            None if entry.name == '.lake/build/bin' else entry)
    with tarfile.open(output, 'r:gz') as archive:
        validate_members(archive.getmembers())


def restore(root: Path, source: Path) -> None:
    if any((root / prefix).exists() for prefix in PREFIXES):
        raise ValueError('restore requires an empty build directory')
    with tarfile.open(source, 'r:gz') as archive:
        members = archive.getmembers()
        validate_members(members)
        if json.load(archive.extractfile(METADATA)) != identity(root):
            raise ValueError('build artifact does not match this checkout and platform')
        for member in members:
            if member.name != METADATA:
                member.mode &= 0o777
                archive.extract(member, root)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode', choices=['pack', 'restore'])
    parser.add_argument('archive', type=Path)
    args = parser.parse_args()
    (pack if args.mode == 'pack' else restore)(ROOT, args.archive.resolve())


if __name__ == '__main__':
    main()
