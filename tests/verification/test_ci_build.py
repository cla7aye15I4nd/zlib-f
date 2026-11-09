#!/usr/bin/env python3
"""Check artifact provenance and complete, disjoint proof mutation scheduling."""
from collections import Counter
import importlib.util
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import tarfile
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'scripts'))
import verification


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


artifact = load('ci_artifact', ROOT / 'scripts/ci-build-artifact.py')
controls = load('audit_controls', ROOT / 'scripts/audit-selftest.py')


class BuildTransport(unittest.TestCase):
    def test_real_lake_refuses_stale_outputs_without_compiling(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'lean-toolchain').write_bytes((ROOT / 'lean-toolchain').read_bytes())
            (root / 'lakefile.toml').write_text('name = "ZlibF"\n[[lean_lib]]\nname = "ZlibF"\n')
            source = root / 'ZlibF.lean'
            source.write_text('def fixture : Nat := 1\n')
            result = subprocess.run(['lake', 'build', 'ZlibF'], cwd=root,
                                    capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            command = ['lake', '--no-build', 'build', 'ZlibF']
            fresh = subprocess.run(command, cwd=root, capture_output=True, text=True)
            self.assertEqual(fresh.returncode, 0, fresh.stdout + fresh.stderr)
            compiled = root / '.lake/build/lib/lean/ZlibF.olean'
            before = compiled.read_bytes()
            source.write_text('def fixture : Nat := 2\n')
            stale = subprocess.run(command, cwd=root, capture_output=True, text=True)
            self.assertNotEqual(stale.returncode, 0, stale.stdout + stale.stderr)
            self.assertEqual(compiled.read_bytes(), before)

    def test_round_trip_and_stale_source_refusal(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            subprocess.run(['git', 'init', '-q', str(root)], check=True)
            (root / 'ZlibF.lean').write_text('def witness := 1\n')
            subprocess.run(['git', 'add', '.'], cwd=root, check=True)
            subprocess.run(['git', '-c', 'user.name=fixture', '-c', 'user.email=fixture@example.invalid',
                            'commit', '-qm', 'Fixture'], cwd=root, check=True)
            compiled = root / '.lake/build/lib/lean/ZlibF.olean'
            compiled.parent.mkdir(parents=True)
            compiled.write_bytes(b'immutable compiled fixture')
            binary = root / 'tests/.lake/build/bin/example'
            binary.parent.mkdir(parents=True)
            binary.write_bytes(b'fixture')
            binary.chmod(0o755)
            unused = root / '.lake/build/bin/auditor'
            unused.parent.mkdir(parents=True)
            unused.write_bytes(b'not transported')
            archive = root / 'outputs.tar.gz'
            artifact.pack(root, archive)
            with tarfile.open(archive, 'r:gz') as contents:
                self.assertNotIn('.lake/build/bin/auditor', contents.getnames())
            with self.assertRaisesRegex(ValueError, 'empty build'):
                artifact.restore(root, archive)
            import shutil
            shutil.rmtree(root / '.lake')
            shutil.rmtree(root / 'tests/.lake')
            artifact.restore(root, archive)
            self.assertEqual(compiled.read_bytes(), b'immutable compiled fixture')
            self.assertEqual(binary.stat().st_mode & 0o777, 0o755)
            shutil.rmtree(root / '.lake')
            shutil.rmtree(root / 'tests/.lake')
            (root / 'ZlibF.lean').write_text('def witness := 2\n')
            with self.assertRaisesRegex(ValueError, 'does not match'):
                artifact.restore(root, archive)
            self.assertFalse((root / '.lake').exists())

    def test_archive_cannot_write_source_traverse_or_link(self):
        for name, kind in [('ZlibF.lean', tarfile.REGTYPE),
                           ('.lake/../../source', tarfile.REGTYPE),
                           ('/absolute', tarfile.REGTYPE),
                           ('.lake/link', tarfile.SYMTYPE),
                           ('.lake/link', tarfile.LNKTYPE)]:
            with self.subTest(name=name, kind=kind), self.assertRaises(ValueError):
                entry = tarfile.TarInfo(name)
                entry.type = kind
                artifact.validate_members([tarfile.TarInfo(artifact.METADATA), entry])
        with self.assertRaises(ValueError):
            artifact.validate_members([])
        with self.assertRaises(ValueError):
            artifact.validate_members([tarfile.TarInfo(artifact.METADATA)] * 2)

    def test_prebuilt_consumers_refuse_to_compile(self):
        with patch.dict(os.environ, {'ZLIBF_REQUIRE_PREBUILT': '1'}), \
                patch.object(verification, 'run') as run:
            verification.build_library()
            run.assert_called_once_with(['lake', '--no-build', 'build', 'ZlibF'])
        with patch.dict(os.environ, {'ZLIBF_REQUIRE_PREBUILT': 'invalid'}), \
                self.assertRaises(verification.Rejected):
            verification.build_library()


class CompleteProofPartition(unittest.TestCase):
    def test_variants_keep_modules_without_copying_native_audit_tools(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            cache = root / 'cache'
            (cache / 'build/bin').mkdir(parents=True)
            (cache / 'build/lib/lean').mkdir(parents=True)
            (cache / 'build/ir').mkdir(parents=True)
            (cache / 'build/bin/auditor').write_bytes(b'not a variant dependency')
            (cache / 'build/lib/lean/Fixture.olean').write_bytes(b'module')
            (cache / 'build/ir/Fixture.c.o').write_bytes(b'native object')
            target = root / 'variant'
            verification.copy_build_cache(cache, target)
            self.assertFalse((target / 'build/bin').exists())
            self.assertEqual((target / 'build/lib/lean/Fixture.olean').read_bytes(), b'module')
            self.assertEqual((target / 'build/ir/Fixture.c.o').read_bytes(), b'native object')
            self.assertEqual((cache / 'build/bin/auditor').read_bytes(), b'not a variant dependency')

    def test_all_real_goals_and_all_rows_exactly_once(self):
        manifest = json.loads((ROOT / verification.MANIFEST).read_text())
        expected_goals, expected_lists = verification.mutation_partition(manifest)
        partitions = [verification.mutation_partition(manifest, 4, index) for index in range(4)]
        self.assertEqual(Counter(goal for goals, _ in partitions for goal in goals),
                         Counter({goal: 1 for goal in expected_goals}))
        expected = Counter((path, row) for path, rows in expected_lists.items() for row in rows)
        actual = Counter((path, row) for _, lists in partitions
                         for path, rows in lists.items() for row in rows)
        self.assertEqual(actual, expected)
        self.assertGreaterEqual(sum(expected.values()), 146)

    def test_invalid_and_empty_partitions_are_errors(self):
        manifest = json.loads((ROOT / verification.MANIFEST).read_text())
        for count, index in [(0, 0), (-1, 0), (4, -1), (4, 4), (10000, 9999)]:
            with self.subTest(count=count, index=index), self.assertRaises(verification.Rejected):
                verification.mutation_partition(manifest, count, index)


class AuditorControls(unittest.TestCase):
    def test_original_control_inventory_and_actual_source_closure(self):
        cases = sorted((ROOT / 'tests/audit/cheats').glob('*.lean')) + \
                sorted((ROOT / 'tests/audit/cheats').glob('*.mut'))
        self.assertEqual(len(cases), 13)
        self.assertEqual({controls.group(case) for case in cases},
                         {'declaration', 'runtime', 'translation', 'statement'})
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            controls.copy_closure(root, list({module for modules in controls.MODULES.values()
                                              for module in modules}))
            for path in root.rglob('*.lean'):
                self.assertEqual(path.read_bytes(), (ROOT / path.relative_to(root)).read_bytes())
            for case in cases:
                if case.suffix == '.mut':
                    path, old, new = case.read_text().rstrip('\n').split('|||')
                    self.assertEqual((root / path).read_text().count(old), 1)
                    self.assertNotEqual(old, new)

    def test_compiler_failure_cannot_count_as_detected(self):
        result = subprocess.CompletedProcess([], 1, stdout='compile failed', stderr='')
        with patch.object(controls.subprocess, 'run', return_value=result), \
                self.assertRaisesRegex(RuntimeError, 'not a rejection'):
            controls.build(ROOT)


if __name__ == '__main__':
    unittest.main()
