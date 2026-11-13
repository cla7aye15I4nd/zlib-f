#!/usr/bin/env python3
"""Exercise the real declaration auditor on small, independently built Lean fixtures."""

import os
import json
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
    @classmethod
    def setUpClass(cls):
        cls.auditor = verification.build_auditor()

    def test_undocumented_functions_are_not_required(self):
        header = ("ZEXTERN int ZEXPORT documented(int);\n" + verification.UNDOCUMENTED_MARK +
                  "\nZEXTERN int ZEXPORT hidden(int);\n")
        self.assertEqual(verification.public_names(header), {"documented", "hidden"})
        self.assertEqual(verification.undocumented_names(header), {"hidden"})
        manifest = {"undocumented": {"functions": ["hidden"]},
                    "apis": [{"function": "documented", "goal": "Goal.documented", "scope": "lp64-linux"},
                             {"function": "hidden", "goal": "Goal.hidden", "scope": "lp64-linux"}]}
        self.assertEqual(verification.required_public_goals(manifest), ["Goal.documented"])

    def test_public_proofs_require_mutants_in_the_actual_function(self):
        source = "ZlibF/Zlib/fixture.c.lean"
        target = self.root / source
        target.parent.mkdir(parents=True)
        target.write_text("namespace Fixture\ndef first : Nat := 0\ndef second : Nat := 2\nend Fixture\n")
        directory = self.root / "tests/proof-mutants"
        directory.mkdir(parents=True)
        table = directory / "fixture.tsv"
        table.write_text("first-change\t" + source + "\tdef first : Nat := 0\tdef first : Nat := 1\tFixture\n"
                         "second-change\t" + source + "\tdef second : Nat := 2\tdef second : Nat := 3\tFixture\n")
        boundary = directory / 'api-boundary.tsv'
        boundary.write_text('api-only\t' + source + '\tdef first : Nat := 0\tdef first : Nat := 4\tFixture\n')
        mapping = self.root / "tests/audit/public-mutants.json"
        mapping.parent.mkdir(parents=True)
        manifest = {"apis": [{"goal": "Goal.first", "function": "first", "source": source,
                              "scope": "lp64-linux"}]}
        report = self.root / "report.txt"
        def write_targets(targets):
            mapping.write_text(json.dumps({"version": 1, "targets": targets}))
        reference = {"list": "tests/proof-mutants/fixture.tsv", "name": "first-change"}
        with patch.object(verification, "ROOT", self.root):
            write_targets({})
            report.write_text("goal Goal.first OPEN\n")
            verification.check_public_mutant_coverage(report, manifest)
            report.write_text("goal Goal.first PROVED by Fixture.exact\n")
            with self.assertRaises(verification.Rejected):
                verification.check_public_mutant_coverage(report, manifest)
            write_targets({"Goal.first": [reference]})
            verification.check_public_mutant_coverage(report, manifest)
            executed = []
            def record(command):
                self.assertEqual(command[:-1], ['env', 'PROOFMUT_STRICT=1',
                                                'bash', 'tests/audit/proofmut.sh'])
                executed.extend(Path(command[-1]).read_text().splitlines())
            with patch.object(verification, "run", side_effect=record), \
                    patch.object(verification, "SAFETY_MUTANT_LISTS", ()), \
                    patch.object(verification, "check_public_mutant_spans"), \
                    patch.object(verification, "replay_public_mutants"):
                verification.run_public_mutants(manifest)
                self.assertCountEqual(executed, table.read_text().splitlines() +
                                      boundary.read_text().splitlines())
            write_targets({"Goal.first": [dict(reference, name="second-change")]})
            with self.assertRaises(verification.Rejected):
                verification.check_public_mutant_coverage(report, manifest)
            write_targets({"Goal.first": [reference]})
            original = table.read_text()
            write_targets({"Goal.first": [dict(reference, name="")]})
            table.write_text(original.replace("first-change", "", 1))
            with self.assertRaises(verification.Rejected):
                verification.check_public_mutant_coverage(report, manifest)
            write_targets({"Goal.first": [reference]})
            table.write_text(original.replace("def first : Nat := 1", "def renamed : Nat := 1"))
            with self.assertRaises(verification.Rejected):
                verification.check_public_mutant_coverage(report, manifest)
            table.write_text(original.replace("\tFixture\n", "\tFixture\tgap:missing proof\n", 1))
            with self.assertRaises(verification.Rejected):
                verification.check_public_mutant_coverage(report, manifest)
            table.write_text(original.replace(source, "ZlibF/Spec/Fixture.lean", 1))
            with self.assertRaises(verification.Rejected):
                verification.check_public_mutant_coverage(report, manifest)
            # a safety goal keys the same function only when it is a registered goal
            table.write_text(original)
            write_targets({"Goal.first_safe": [reference]})
            with self.assertRaises(verification.Rejected):
                verification.public_mutants(manifest)
            (self.root / "tests/audit/goals.txt").write_text("Goal.first\nGoal.first_safe\n")
            self.assertIn("Goal.first_safe", verification.public_mutants(manifest))
            write_targets({"Goal.first_safe": [dict(reference, name="second-change")]})
            with self.assertRaises(verification.Rejected):
                verification.public_mutants(manifest)
            write_targets({"Goal.first_safety": [reference]})
            with self.assertRaises(verification.Rejected):
                verification.public_mutants(manifest)


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

    def audit(self, strict=False, compare=True):
        args = ["lake", "env", str(self.auditor),
                str(self.theorems), str(self.goals), str(ROOT / "tests/audit/compiler-helpers.txt")]
        if compare:
            args.append("--compare-axiom-collectors")
        if strict:
            args.append("--require-complete")
        return subprocess.run(args, cwd=self.root, text=True, capture_output=True)

    def test_invalid_declaration_rejects_without_success_report(self):
        self.source.write_text(FIXTURE + "\nnamespace ZlibF.Fixture\naxiom invalid : False\nend ZlibF.Fixture\n")
        self.build()
        result = self.audit(compare=False)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("axiom ZlibF.Fixture.invalid", result.stderr)
        self.assertEqual(result.stdout, "")

    def test_native_report_matches_interpreter(self):
        native = self.audit()
        interpreted = subprocess.run(
            ["lake", "env", "lean", "--run", str(ROOT / "tests/audit/Audit.lean"),
             str(self.theorems), str(self.goals), str(ROOT / "tests/audit/compiler-helpers.txt"),
             "--compare-axiom-collectors"], cwd=self.root, text=True, capture_output=True)
        self.assertEqual(native.returncode, 0, native.stdout + native.stderr)
        self.assertEqual(interpreted.returncode, native.returncode, interpreted.stderr)
        self.assertEqual(interpreted.stdout, native.stdout)

    def test_collector_follows_private_values_and_axiom_types(self):
        self.source.write_text(FIXTURE + """
namespace ZlibF.Fixture
axiom forbiddenType : Prop
axiom forbiddenValue : forbiddenType
private def hiddenProof : forbiddenType := forbiddenValue
def indirectProof : forbiddenType := hiddenProof
end ZlibF.Fixture
""")
        self.build()
        result = self.audit()
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("indirectProof depends on", result.stderr)
        self.assertIn("forbiddenType", result.stderr)
        self.assertIn("forbiddenValue", result.stderr)
        self.assertNotIn("collector disagreement", result.stderr)

    def test_collector_handles_mutual_inductive_cycles(self):
        self.source.write_text(FIXTURE + """
namespace ZlibF.Fixture
axiom forbiddenSize : Nat
mutual
  inductive ChainA where
    | next : ChainB → ChainA
  inductive ChainB where
    | next : Fin (forbiddenSize + 1) → ChainA → ChainB
end
def usesA : Type := ChainA
def usesB : Type := ChainB
end ZlibF.Fixture
""")
        self.build()
        result = self.audit()
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("usesA depends on", result.stderr)
        self.assertIn("usesB depends on", result.stderr)
        self.assertNotIn("collector disagreement", result.stderr)

    def test_audit_builds_tool_from_invoking_snapshot(self):
        directory = self.root / "tests/audit"
        directory.mkdir(parents=True)
        (directory / "goals.txt").write_text(self.goals.read_text())
        (directory / "Audit.lean").write_text("def main : IO UInt32 := pure 0\n")
        completed = subprocess.CompletedProcess([], 0)
        with patch.object(verification, "ROOT", self.root), \
                patch.object(verification.subprocess, "run", return_value=completed) as runner:
            self.assertEqual(verification.audit(self.root / "report.txt"), 0)
        self.assertEqual(runner.call_args_list[0].kwargs["cwd"], ROOT)
        self.assertEqual(runner.call_args_list[0].args[0], ["lake", "build", "zlibf-audit"])
        self.assertEqual(runner.call_args_list[1].kwargs["cwd"], self.root)
        self.assertEqual(runner.call_args_list[1].args[0][:3], ["lake", "env", str(self.auditor)])

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

    def test_proof_namespace_definition_is_reported(self):
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

    def test_private_dependency_is_reported(self):
        before = self.audit()
        self.source.write_text(FIXTURE.replace("hidden : Nat := 7", "hidden : Nat := 8"))
        self.build()
        after = self.audit()
        self.assertEqual(before.returncode, 0, before.stdout + before.stderr)
        self.assertEqual(after.returncode, 0, after.stdout + after.stderr)
        old = [s for s in before.stdout.splitlines() if s.startswith("trusted ")]
        new = [s for s in after.stdout.splitlines() if s.startswith("trusted ")]
        self.assertNotEqual(old, new)


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
        nested_dir = self.root / "ZlibF/Proof/Api"
        nested_dir.mkdir()
        (nested_dir / "fixture.c.lean").write_text(
            "import ZlibF.Zlib.«fixture.c»\nnamespace Fixture\n"
            "theorem nestedChecked : value = 0 := rfl\nend Fixture\n")
        mutations.write_text("nested-killed\tZlibF/Zlib/fixture.c.lean\tdef value : Nat := 0\t"
                             "def value : Nat := 1\tApi/fixture.c\n")
        nested = mutants(1)
        self.assertEqual(nested.returncode, 0, nested.stdout + nested.stderr)
        self.assertIn("KILLED", nested.stdout)
        empty = mutants(1, "no-match")
        self.assertNotEqual(empty.returncode, 0, empty.stdout + empty.stderr)


if __name__ == "__main__":
    unittest.main()
