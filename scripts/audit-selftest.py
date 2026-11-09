#!/usr/bin/env python3
"""Test the auditor on small closures of the unchanged actual project source.

The separate mandatory audit_core checks the whole library and committed locks.
A build failure or crashed auditor is a harness error, never a detected cheat.
"""
from __future__ import annotations
import importlib.util
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import time
import verification

ROOT = Path(__file__).resolve().parents[1]
MODULES = {
    'declaration': ['ZlibF.Runtime.Libc', 'ZlibF.Runtime.Tables'],
    'runtime': ['ZlibF.Runtime.Ptr'],
    'translation': ['ZlibF.Zlib.«adler32.c»'],
    'statement': ['ZlibF.Proof.«zutil.c»'],
}
MUTATIONS = {
    'touch_runtime.mut': 'runtime', 'weaken_runtime.mut': 'runtime',
    'change_translation.mut': 'translation', 'change_statement.mut': 'statement',
}
WITNESS = '''namespace ZlibF.AuditFixture
def Goal.checked : Prop := True
/-- A positive auditor control, not a zlib correctness claim. -/
theorem witness : Goal.checked := True.intro
end ZlibF.AuditFixture
'''


def group(case: Path) -> str:
    return 'declaration' if case.suffix == '.lean' else MUTATIONS[case.name]


def module_path(name: str) -> Path:
    parts = [part.strip('«»') for part in re.findall(r'«[^»]+»|[^.]+', name)]
    if not parts or parts[0] != 'ZlibF' or any(
            not part or part in {'.', '..'} or '/' in part or '\\' in part for part in parts):
        raise ValueError('invalid local import: ' + name)
    return Path(*parts[:-1], parts[-1] + '.lean')


def copy_closure(destination: Path, modules: list[str]) -> None:
    pending, seen = list(modules), set()
    while pending:
        module = pending.pop()
        if module in seen:
            continue
        seen.add(module)
        path = module_path(module)
        source = ROOT / path
        if source.is_symlink() or not source.is_file():
            raise ValueError('missing ordinary source: ' + str(path))
        target = destination / path
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(source, target)
        for imports in re.findall(r'^\s*(?:public\s+)?import\s+(.+)$', source.read_text(), re.M):
            pending.extend(name for name in imports.split('--', 1)[0].split()
                           if name == 'ZlibF' or name.startswith('ZlibF.'))


def build(root: Path) -> None:
    result = subprocess.run(['lake', 'build', 'ZlibF'], cwd=root,
                            text=True, capture_output=True, timeout=180)
    if result.returncode:
        raise RuntimeError('control did not compile (not a rejection):\n' + result.stdout + result.stderr)


def audit(root: Path, binary: Path, report: Path) -> subprocess.CompletedProcess:
    with report.open('w') as out:
        return subprocess.run(['lake', 'env', str(binary), 'tests/audit/theorems.txt',
                               'tests/audit/goals.txt'], cwd=root, stdout=out,
                              stderr=subprocess.PIPE, text=True, timeout=180)


def locks(root: Path, report: Path, *, regenerate: bool = False) -> None:
    previous = verification.ROOT
    try:
        verification.ROOT = root
        verification.check_locks(report, regenerate=regenerate)
    finally:
        verification.ROOT = previous


def baseline(root: Path, kind: str, binary: Path, cache: Path | None = None) -> None:
    root.mkdir()
    shutil.copy2(ROOT / 'lean-toolchain', root / 'lean-toolchain')
    (root / 'lakefile.toml').write_text('name = "ZlibF"\n[[lean_lib]]\nname = "ZlibF"\n')
    copy_closure(root, MODULES[kind])
    (root / 'ZlibF/AuditFixture.lean').write_text(WITNESS)
    (root / 'ZlibF.lean').write_text(''.join('import ' + name + '\n' for name in MODULES[kind]) +
                                    'import ZlibF.AuditFixture\n')
    directory = root / 'tests/audit'
    directory.mkdir(parents=True)
    names = ['ZlibF.AuditFixture.witness']
    if kind == 'statement':
        names.append('Zlib.Zutil.Proofs.zlibVersion_safe')
    (directory / 'theorems.txt').write_text('\n'.join(names) + '\n')
    (directory / 'goals.txt').write_text('ZlibF.AuditFixture.Goal.checked\n')
    shutil.copy2(ROOT / 'tests/audit/compiler-helpers.txt', directory / 'compiler-helpers.txt')
    if cache is not None:
        shutil.copytree(cache, root / '.lake')
    build(root)
    report = root / 'baseline.txt'
    result = audit(root, binary, report)
    if result.returncode:
        raise RuntimeError('positive control rejected:\n' + result.stderr)
    locks(root, report, regenerate=True)
    locks(root, report)
    print(f'baseline {kind}: {len(list((root / "ZlibF").rglob("*.lean")))} actual source modules', flush=True)


def run_case(base: Path, root: Path, case: Path, binary: Path) -> None:
    shutil.copytree(base, root)
    if case.suffix == '.lean':
        shutil.copy2(case, root / 'ZlibF/Cheat.lean')
        with (root / 'ZlibF.lean').open('a') as out:
            out.write('import ZlibF.Cheat\n')
    else:
        path, old, new = case.read_text().rstrip('\n').split('|||')
        relative = Path(path)
        if relative.is_absolute() or '..' in relative.parts:
            raise ValueError('invalid mutation source')
        target = root / relative
        content = target.read_text()
        if not old or old == new or content.count(old) != 1:
            raise ValueError('mutation must change exactly one occurrence: ' + case.name)
        target.write_text(content.replace(old, new, 1))
    build(root)
    report = root / 'mutant.txt'
    result = audit(root, binary, report)
    if case.suffix == '.lean':
        if result.returncode != 1 or 'PROBLEM:' not in report.read_text() + result.stderr:
            raise RuntimeError('cheat survived or auditor failed unexpectedly: ' + case.name + '\n' + result.stderr)
    else:
        if result.returncode:
            raise RuntimeError('semantic control audit failed unexpectedly: ' + case.name + '\n' + result.stderr)
        expected = 'statements.lock' if group(case) == 'statement' else 'trusted.lock'
        try:
            locks(base, report)
        except verification.Rejected as error:
            if str(error) != 'semantic lock differs: tests/audit/' + expected:
                raise
        else:
            raise RuntimeError('semantic change survived: ' + case.name)


def main() -> None:
    started_all = time.monotonic()
    spec = importlib.util.spec_from_file_location('audit_shards', ROOT / 'scripts/select-audit-cheats.py')
    selector = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(selector)
    cases = selector.select(ROOT / 'tests/audit/cheats',
                            int(os.environ.get('AUDIT_SHARD_COUNT', '1')),
                            int(os.environ.get('AUDIT_SHARD_INDEX', '0')))
    binary = verification.build_auditor()
    with tempfile.TemporaryDirectory(prefix='audit-unit-controls-') as directory:
        parent = Path(directory)
        kinds = sorted({group(case) for case in cases})
        # Compile unchanged common dependencies once, then copy that immutable
        # cache into each smaller import root. Never share writable build files.
        MODULES['seed'] = sorted({name for kind in kinds for name in MODULES[kind]})
        baseline(parent / 'seed', 'seed', binary)
        for kind in kinds:
            baseline(parent / kind, kind, binary, parent / 'seed/.lake')
        for index, case in enumerate(cases):
            started = time.monotonic()
            destination = parent / ('case-' + str(index))
            run_case(parent / group(case), destination, case, binary)
            shutil.rmtree(destination)
            print(f'rejected {case.name} ({time.monotonic() - started:.2f}s)', flush=True)
    print(f'{len(cases)} controls passed in {time.monotonic() - started_all:.2f}s', flush=True)


if __name__ == '__main__':
    try:
        main()
    except (OSError, ValueError, RuntimeError, KeyError, subprocess.SubprocessError) as error:
        print('AUDIT SELFTEST ERROR: ' + str(error), file=sys.stderr)
        sys.exit(1)
