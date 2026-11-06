"""Check that one mutation suite cannot contaminate the next positive baseline."""

import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[2]


class HarnessIsolation(unittest.TestCase):
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
            for name in ("selftest.sh", "mutate.py"):
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


if __name__ == "__main__":
    unittest.main()
