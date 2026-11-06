#!/usr/bin/env python3
"""Exercise the real declaration auditor on small, independently built Lean fixtures."""

import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest
from unittest.mock import patch
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts"))
import verification
FIXTURE = """namespace ZlibF.Fixture
namespace Proofs
def condition : Prop := True
private def hidden : Nat := 7
def surface : Nat := hidden
end Proofs
def Goal.checked : Prop := True
/-- Exact proof used to test final acceptance. -/
theorem exact : Goal.checked := True.intro
/-- A stronger premise must not count as the original target. -/
theorem stronger (_extra : True) : Goal.checked := True.intro
end ZlibF.Fixture
"""


class AuditTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="declaration-audit-test-")
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        shutil.copyfile(ROOT / "lean-toolchain", self.root / "lean-toolchain")
        (self.root / "lakefile.toml").write_text('name = "ZlibF"\n[[lean_lib]]\nname = "ZlibF"\n')
        (self.root / "ZlibF").mkdir()
        (self.root / "ZlibF.lean").write_text("import ZlibF.Fixture\n")
        self.source = self.root / "ZlibF/Fixture.lean"
        self.source.write_text(FIXTURE)
        self.theorems = self.root / "theorems.txt"
        self.goals = self.root / "goals.txt"
        self.theorems.write_text("ZlibF.Fixture.exact\n")
        self.goals.write_text("ZlibF.Fixture.Goal.checked\n")
        self.build()

    def build(self):
        result = subprocess.run(["lake", "build", "ZlibF"], cwd=self.root, text=True,
                                capture_output=True)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def audit(self, strict=False):
        args = ["lake", "env", "lean", "--run", str(ROOT / "tests/audit/Audit.lean"),
                str(self.theorems), str(self.goals), str(ROOT / "tests/audit/compiler-helpers.txt")]
        if strict:
            args.append("--require-complete")
        return subprocess.run(args, cwd=self.root, text=True, capture_output=True)

    def test_exact_target_passes_strict(self):
        result = self.audit(strict=True)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("PROVED by ZlibF.Fixture.exact", result.stdout)

    def test_extra_premise_stays_open(self):
        self.theorems.write_text("ZlibF.Fixture.stronger\n")
        progress = self.audit()
        self.assertEqual(progress.returncode, 0, progress.stdout + progress.stderr)
        self.assertIn("Goal.checked OPEN", progress.stdout)
        strict = self.audit(strict=True)
        self.assertNotEqual(strict.returncode, 0)
        self.assertIn("unproved goal", strict.stdout + strict.stderr)

    def test_proof_namespace_definition_is_locked(self):
        before = self.audit()
        self.assertEqual(before.returncode, 0, before.stdout + before.stderr)
        self.assertIn("trusted ZlibF.Fixture.Proofs.condition ", before.stdout)
        self.source.write_text(FIXTURE.replace("condition : Prop := True", "condition : Prop := False"))
        self.build()
        after = self.audit()
        self.assertEqual(after.returncode, 0, after.stdout + after.stderr)
        old = [s for s in before.stdout.splitlines() if s.startswith("trusted ")]
        new = [s for s in after.stdout.splitlines() if s.startswith("trusted ")]
        self.assertNotEqual(old, new)

    def test_private_dependency_is_locked(self):
        before = self.audit()
        self.source.write_text(FIXTURE.replace("hidden : Nat := 7", "hidden : Nat := 8"))
        self.build()
        after = self.audit()
        self.assertEqual(before.returncode, 0, before.stdout + before.stderr)
        self.assertEqual(after.returncode, 0, after.stdout + after.stderr)
        old = [s for s in before.stdout.splitlines() if s.startswith("trusted ")]
        new = [s for s in after.stdout.splitlines() if s.startswith("trusted ")]
        self.assertNotEqual(old, new)

    def test_full_syntax_uses_cryptographic_locks(self):
        result = self.audit()
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        report = self.root / "report.txt"
        report.write_text(result.stdout)
        (self.root / "tests/audit").mkdir(parents=True)
        with patch.object(verification, "ROOT", self.root):
            verification.check_locks(report, regenerate=True)
            verification.check_locks(report)
            trusted = (self.root / "tests/audit/trusted.lock").read_text()
            self.assertRegex(trusted, r"trusted \S+ [0-9a-f]{64} [0-9a-f]{64}")
            report.write_text("\n".join(s for s in result.stdout.splitlines()
                                        if not s.startswith("semantic ")))
            with self.assertRaises(verification.Rejected):
                verification.check_locks(report)

    def test_proof_body_can_change_without_changing_locks(self):
        before = self.audit()
        self.assertEqual(before.returncode, 0, before.stdout + before.stderr)
        report = self.root / "report.txt"
        report.write_text(before.stdout)
        (self.root / "tests/audit").mkdir(parents=True)
        with patch.object(verification, "ROOT", self.root):
            verification.check_locks(report, regenerate=True)
            self.source.write_text(FIXTURE.replace(
                "theorem exact : Goal.checked := True.intro",
                "theorem exact : Goal.checked := by\n  have h : True := True.intro\n  exact h"))
            self.build()
            after = self.audit()
            self.assertEqual(after.returncode, 0, after.stdout + after.stderr)
            report.write_text(after.stdout)
            verification.check_locks(report)

    def test_new_exact_proof_extends_the_baseline(self):
        pending = "\nnamespace ZlibF.Fixture\ndef Goal.pending : Prop := True\nend ZlibF.Fixture\n"
        self.source.write_text(FIXTURE + pending)
        self.goals.write_text(self.goals.read_text() + "ZlibF.Fixture.Goal.pending\n")
        self.build()
        before = self.audit()
        self.assertEqual(before.returncode, 0, before.stdout + before.stderr)
        self.assertIn("Goal.pending OPEN", before.stdout)
        report = self.root / "report.txt"
        report.write_text(before.stdout)
        (self.root / "tests/audit").mkdir(parents=True)
        with patch.object(verification, "ROOT", self.root):
            verification.check_locks(report, regenerate=True)
            old_types = verification.statement_records(
                (self.root / "tests/audit/statements.lock").read_text())
            old_trusted = (self.root / "tests/audit/trusted.lock").read_bytes()
            proof = "\nnamespace ZlibF.Fixture\n/-- Newly completed fixed target. -/\n" \
                    "theorem completed : Goal.pending := True.intro\nend ZlibF.Fixture\n"
            self.source.write_text(FIXTURE + pending + proof)
            self.theorems.write_text(self.theorems.read_text() + "ZlibF.Fixture.completed\n")
            self.build()
            after = self.audit(strict=True)
            self.assertEqual(after.returncode, 0, after.stdout + after.stderr)
            report.write_text(after.stdout)
            verification.check_locks(report, regenerate=True)
            self.assertEqual(old_trusted, (self.root / "tests/audit/trusted.lock").read_bytes())
            new_types = verification.statement_records(
                (self.root / "tests/audit/statements.lock").read_text())
            verification.check_proof_extensions(set(old_types), old_types, set(new_types), new_types)
            with self.assertRaisesRegex(verification.Rejected, "removed"):
                verification.check_proof_extensions(set(old_types), old_types,
                    {"ZlibF.Fixture.completed"}, {"ZlibF.Fixture.completed": new_types["ZlibF.Fixture.completed"]})
            changed = dict(new_types)
            changed["ZlibF.Fixture.exact"] = "0" * 64 + " :: True"
            with self.assertRaisesRegex(verification.Rejected, "type changed"):
                verification.check_proof_extensions(set(old_types), old_types, set(changed), changed)
            with self.assertRaisesRegex(verification.Rejected, "disagree"):
                verification.check_proof_extensions(set(old_types), old_types, set(old_types), new_types)

    def test_missing_registry_is_rejected(self):
        self.goals.unlink()
        self.assertNotEqual(self.audit().returncode, 0)

    def test_empty_registry_is_rejected(self):
        self.goals.write_text("# no targets\n")
        self.assertNotEqual(self.audit().returncode, 0)

    def test_duplicate_goal_is_rejected(self):
        self.goals.write_text("ZlibF.Fixture.Goal.checked\n" * 2)
        self.assertNotEqual(self.audit().returncode, 0)

    def test_duplicate_theorem_is_rejected(self):
        self.theorems.write_text("ZlibF.Fixture.exact\n" * 2)
        self.assertNotEqual(self.audit().returncode, 0)

    def test_unregistered_goal_is_rejected(self):
        self.source.write_text(FIXTURE + "\nnamespace ZlibF.Fixture\ndef Goal.omitted : Prop := True\nend ZlibF.Fixture\n")
        self.build()
        result = self.audit()
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("unregistered goal ZlibF.Fixture.Goal.omitted", result.stdout + result.stderr)

    def test_unapproved_assumption_is_rejected(self):
        self.source.write_text(FIXTURE + "\nnamespace ZlibF.Fixture\naxiom unsupported : False\nend ZlibF.Fixture\n")
        self.build()
        result = self.audit()
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("axiom ZlibF.Fixture.unsupported", result.stdout + result.stderr)

    def test_private_unsupported_definition_is_rejected(self):
        self.source.write_text(FIXTURE + "\nnamespace ZlibF.Fixture\nprivate unsafe def badPrivate : Nat := 0\nend ZlibF.Fixture\n")
        self.build()
        result = self.audit()
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("unsafe declaration", result.stdout + result.stderr)

    def test_final_mutants_reject_known_gaps(self):
        audit_dir = self.root / "tests/audit"
        audit_dir.mkdir(parents=True)
        shutil.copyfile(ROOT / "tests/audit/proofmut.sh", audit_dir / "proofmut.sh")
        (self.root / "ZlibF/Zlib").mkdir()
        (self.root / "ZlibF/Proof").mkdir()
        (self.root / "ZlibF/Zlib/fixture.c.lean").write_text(
            "namespace Fixture\ndef value : Nat := 0\ndef unused : Nat := 0\nend Fixture\n")
        (self.root / "ZlibF/Proof/fixture.c.lean").write_text(
            "import ZlibF.Zlib.«fixture.c»\nnamespace Fixture\n"
            "theorem checked : value = 0 := rfl\nend Fixture\n")
        mutations = audit_dir / "fixture.tsv"
        mutations.write_text("known-gap\tZlibF/Zlib/fixture.c.lean\tdef unused : Nat := 0\t"
                             "def unused : Nat := 1\tfixture.c\tgap:deliberately uncovered fixture\n")

        def mutants(strict, pattern="."):
            env = dict(os.environ, PROOFMUT_STRICT=str(strict), PROOFMUT_BASELINE="0")
            return subprocess.run(["bash", "tests/audit/proofmut.sh", str(mutations), pattern],
                                  cwd=self.root, env=env, text=True, errors="replace", capture_output=True)

        development = mutants(0)
        self.assertEqual(development.returncode, 0, development.stdout + development.stderr)
        self.assertIn("GAP (known)", development.stdout)
        final = mutants(1)
        self.assertNotEqual(final.returncode, 0, final.stdout + final.stderr)
        self.assertIn("baseline: the listed proof modules build unmutated", final.stdout)
        self.assertIn("strict acceptance requires", final.stdout)
        mutations.write_text("killed\tZlibF/Zlib/fixture.c.lean\tdef value : Nat := 0\t"
                             "def value : Nat := 1\tfixture.c\n")
        killed = mutants(1)
        self.assertEqual(killed.returncode, 0, killed.stdout + killed.stderr)
        self.assertIn("KILLED", killed.stdout)
        empty = mutants(1, "no-match")
        self.assertNotEqual(empty.returncode, 0, empty.stdout + empty.stderr)


if __name__ == "__main__":
    unittest.main()
