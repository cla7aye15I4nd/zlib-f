"""Check that one mutation suite cannot contaminate the next positive baseline."""

import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[2]


class HarnessIsolation(unittest.TestCase):
    def test_preflight_checks_the_translation_before_running_mutants(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            tables = root / "tests/mutations"
            tables.mkdir(parents=True)
            source = root / "function.lean"
            original = "namespace Zlib.Fixture\ndef value := 1\nend Zlib.Fixture\n" \
                       "def proofOnly := 2\n"
            source.write_text(original)
            table = tables / "fixture.tsv"
            def check(selected=""):
                return subprocess.run(
                    [sys.executable, str(ROOT / "tests/mutate.py"), "--check-lists", str(root), selected],
                    text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=10)
            table.write_text("valid\tdetect\tfunction.lean\t1\tdef value := 1\tdef value := 3\n")
            valid = check()
            self.assertEqual(valid.returncode, 0, valid.stdout)
            self.assertEqual(source.read_text(), original)
            table.write_text("stale\tdetect\tfunction.lean\t1\tdef proofOnly := 2\tdef proofOnly := 3\n")
            stale = check()
            self.assertNotEqual(stale.returncode, 0, stale.stdout)
            self.assertIn("fixture.tsv:1", stale.stdout)
            self.assertNotEqual(check("missing").returncode, 0)

    def test_last_mutant_is_restored_between_suites(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            tests = root / "tests"
            mutations = tests / "mutations"
            mutations.mkdir(parents=True)
            (root / "ZlibF").mkdir()
            library = root / "library"
            library.mkdir()
            (library / "libz.a").touch()
            for name in ("selftest.sh", "selftest-parallel.sh", "mutate.py"):
                shutil.copy2(ROOT / "tests" / name, tests / name)
            for name in ("a", "b"):
                (root / "ZlibF" / f"{name}.lean").write_text(
                    f"namespace Zlib.{name}\ndef value := 1\nend Zlib.{name}\n"
                )
                (mutations / f"{name}.tsv").write_text(
                    f"change-{name}\tdetect\tZlibF/{name}.lean\t1\tdef value := 1\tdef value := 2\n"
                )
            # A small deterministic runner isolates the shell's suite orchestration. The real
            # differential runner remains the positive baseline in the integration self test.
            (tests / "run.sh").write_text(
                "#!/usr/bin/env bash\n"
                "set -eu\n"
                "for file in \"$(dirname \"$0\")/../ZlibF/\"*.lean; do\n"
                "  if grep -q 'def value := 2' \"$file\"; then\n"
                "    echo 'DIFFERENCE: observed changed value'; exit 1\n"
                "  fi\n"
                "done\n"
                "echo 'PASS: positive baseline'\n"
            )
            env = dict(os.environ, ZLIB_BUILD=str(library))
            env.pop("ONLY", None)
            result = subprocess.run(
                ["bash", str(tests / "selftest.sh")], cwd=root, env=env,
                text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=30,
            )
            self.assertEqual(result.returncode, 0, result.stdout)
            self.assertEqual(result.stdout.count("PASS: positive baseline"), 2, result.stdout)
            self.assertIn("2 mutations that must be detected", result.stdout)
            parallel = subprocess.run(
                ["bash", str(tests / "selftest-parallel.sh")], cwd=root, env=env,
                text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=30)
            self.assertEqual(parallel.returncode, 0, parallel.stdout)
            self.assertEqual(parallel.stdout.count("PASS: positive baseline"), 4, parallel.stdout)
            self.assertEqual(parallel.stdout.count("change-a "), 1, parallel.stdout)
            self.assertEqual(parallel.stdout.count("change-b "), 1, parallel.stdout)
            original_runner = (tests / "run.sh").read_text()
            (tests / "run.sh").write_text(original_runner.replace("set -eu\n",
                'set -eu\nif [ "${MUTATION_SHARD_INDEX:-0}" = 1 ]; then exit 2; fi\n'))
            failed = subprocess.run(
                ["bash", str(tests / "selftest-parallel.sh")], cwd=root, env=env,
                text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=30)
            self.assertNotEqual(failed.returncode, 0, failed.stdout)
            self.assertIn("SELFTEST FAILED", failed.stdout)


if __name__ == "__main__":
    unittest.main()
