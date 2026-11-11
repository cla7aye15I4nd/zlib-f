#!/usr/bin/env python3
"""Check the real negative-sample partition and its fail-closed boundaries."""
from collections import Counter
import importlib.util
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
SELECTOR = ROOT / 'scripts/select-audit-cheats.py'
spec = importlib.util.spec_from_file_location('audit_shards', SELECTOR)
shards = importlib.util.module_from_spec(spec)
spec.loader.exec_module(shards)


class AuditShards(unittest.TestCase):
    def test_complete_nonoverlapping_ci_partition(self):
        directory = ROOT / 'tests/audit/cheats'
        expected = {p for p in directory.iterdir() if p.suffix == '.lean'}
        actual = [p for index in range(2) for p in shards.select(directory, 2, index)]
        self.assertEqual(Counter(actual), Counter({p: 1 for p in expected}))
        self.assertEqual(set(shards.select(directory, 1, 0)), expected)

    def test_invalid_coordinates_and_empty_shards_fail(self):
        directory = ROOT / 'tests/audit/cheats'
        for count, index in [(0, 0), (-1, 0), (2, -1), (2, 2), (1000, 999)]:
            with self.subTest(count=count, index=index), self.assertRaises(ValueError):
                shards.select(directory, count, index)
        for count, index in [('invalid', '0'), ('', '0'), ('2', '')]:
            result = subprocess.run([sys.executable, str(SELECTOR), str(directory), count, index],
                                    capture_output=True, text=True)
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, '')

    def test_empty_and_nonordinary_inventories_fail(self):
        with tempfile.TemporaryDirectory() as temp:
            directory = Path(temp)
            with self.assertRaises(ValueError):
                shards.select(directory, 1, 0)
            (directory / 'fake.lean').mkdir()
            with self.assertRaises(ValueError):
                shards.select(directory, 1, 0)
            (directory / 'fake.lean').rmdir()
            (directory / 'real.txt').write_text('fixture')
            (directory / 'link.lean').symlink_to(directory / 'real.txt')
            with self.assertRaises(ValueError):
                shards.select(directory, 1, 0)


if __name__ == '__main__':
    unittest.main()
