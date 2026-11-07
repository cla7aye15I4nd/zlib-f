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
            with patch.object(verification, "run") as runner, \
                    patch.object(verification, "check_public_mutant_spans"), \
                    patch.object(verification, "replay_public_mutants"):
                verification.run_public_mutants(manifest)
                executed = {call.args[0][-1] for call in runner.call_args_list}
                self.assertEqual(executed, {"tests/proof-mutants/fixture.tsv",
                                            "tests/proof-mutants/api-boundary.tsv"})
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

    def test_locked_inputs_must_be_versioned(self):
        policy = {"files": {"tests/lake-manifest.json": "digest", "ZlibF.lean": "digest"}}
        with patch.object(verification.subprocess, "check_output", return_value="ZlibF.lean\0"):
            with self.assertRaisesRegex(verification.Rejected, "tests/lake-manifest.json"):
                verification.check_versioned_sources(policy)
        with patch.object(verification.subprocess, "check_output",
                          return_value="ZlibF.lean\0tests/lake-manifest.json\0"):
            verification.check_versioned_sources(policy)

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

    def test_proof_index_accepts_theorems_but_locks_new_definitions(self):
        self.source.write_text(FIXTURE +
            "\nnamespace ZlibF.Fixture\ndef Goal.pending : Prop := True\nend ZlibF.Fixture\n")
        self.goals.write_text(self.goals.read_text() + "ZlibF.Fixture.Goal.pending\n")
        proof_dir = self.root / "ZlibF/Proof"
        proof_dir.mkdir()
        index = proof_dir / "Index.lean"
        index.write_text("-- Proof-only import point.\n")
        root_source = "import ZlibF.Fixture\nimport ZlibF.Proof.Index\n"
        (self.root / "ZlibF.lean").write_text(root_source)
        self.build()
        before = self.audit()
        self.assertEqual(before.returncode, 0, before.stdout + before.stderr)
        report = self.root / "report.txt"
        report.write_text(before.stdout)
        (self.root / "tests/audit").mkdir(parents=True)
        with patch.object(verification, "ROOT", self.root):
            verification.check_locks(report, regenerate=True)
            old_trusted = (self.root / "tests/audit/trusted.lock").read_bytes()
            proof = proof_dir / "New.lean"
            theorem = "import ZlibF.Fixture\nnamespace ZlibF.Fixture\n/-- New fixed-target proof. -/\n" \
                      "theorem completed : Goal.pending := True.intro\nend ZlibF.Fixture\n"
            proof.write_text(theorem)
            index.write_text("import ZlibF.Proof.New\n")
            self.theorems.write_text(self.theorems.read_text() + "ZlibF.Fixture.completed\n")
            self.build()
            after = self.audit(strict=True)
            self.assertEqual(after.returncode, 0, after.stdout + after.stderr)
            report.write_text(after.stdout)
            verification.check_locks(report, regenerate=True)
            self.assertEqual(old_trusted, (self.root / "tests/audit/trusted.lock").read_bytes())
            self.assertEqual(root_source, (self.root / "ZlibF.lean").read_text())
            proof.write_text(theorem + "namespace ZlibF.Fixture\n"
                             "private def importedCondition : Prop := True\nend ZlibF.Fixture\n")
            self.build()
            changed = self.audit(strict=True)
            self.assertEqual(changed.returncode, 0, changed.stdout + changed.stderr)
            report.write_text(changed.stdout)
            with self.assertRaises(verification.Rejected):
                verification.check_locks(report)

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


class PolicyLayoutTests(unittest.TestCase):
    def test_legacy_and_current_layouts_are_explicit(self):
        self.assertEqual(verification.layout_files({"apis": [{"manual": "docs/spec/queries.md#version"}]}), ())
        self.assertEqual(verification.layout_files({"apis": [{"manual": "docs/api/utility.md#version"}]}),
                         verification.CURRENT_LAYOUT_FILES)

    def test_nested_spec_layout_keeps_current_normative_files(self):
        self.assertEqual(verification.layout_files({"apis": [{"manual": "docs/spec/api/utility.md#version"}]}),
                         verification.SPEC_LAYOUT_FILES)
        self.assertTrue(set(verification.CURRENT_LAYOUT_FILES) <= set(verification.SPEC_LAYOUT_FILES))

    def test_mixed_empty_and_unknown_layouts_are_rejected(self):
        for paths in [[], ["docs/spec/a.md", "docs/api/b.md"], ["docs/other/a.md"],
                      ["docs/spec/api/a.md", "docs/spec/b.md"],
                      ["docs/spec/api/a.md", "docs/api/b.md"]]:
            with self.subTest(paths=paths), self.assertRaises(verification.Rejected):
                verification.layout_files({"apis": [{"manual": path + "#entry"} for path in paths]})

    def test_current_layout_requires_and_locks_every_normative_file(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            manifest = root / verification.MANIFEST
            manifest.parent.mkdir(parents=True)
            manifest.write_text(json.dumps({"apis": [{"manual": "docs/api/utility.md#version"}]}))
            (root / "ZlibF.lean").write_text("-- fixture\n")
            for name in ["docs/spec/legacy.md", "docs/api/utility.md", "docs/format/grammar.md"]:
                target = root / name
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_text("fixture\n")
            with patch.object(verification, "ROOT", root), \
                    patch.object(verification, "FIXED_FILES", ("ZlibF.lean",)), \
                    patch.object(verification, "FIXED_DIRS", ("docs/spec", "docs/api", "docs/format", "tests/audit")), \
                    patch.object(verification.subprocess, "check_output", return_value="160000 " + "a" * 40 + " 0\tzlib\n"):
                with self.assertRaisesRegex(verification.Rejected, "protected file missing"):
                    verification.source_policy()
                for name in verification.CURRENT_LAYOUT_FILES:
                    target = root / name
                    target.parent.mkdir(parents=True, exist_ok=True)
                    target.write_text("normative fixture\n")
                files = verification.source_policy()["files"]
                self.assertTrue(set(verification.CURRENT_LAYOUT_FILES) <= set(files))
                self.assertTrue({"docs/spec/legacy.md", "docs/api/utility.md", "docs/format/grammar.md"} <= set(files))
                (root / "docs/checking/goals.md").unlink()
                with self.assertRaisesRegex(verification.Rejected, "protected file missing"):
                    verification.source_policy()

    def test_nested_layout_locks_both_specifications_and_review_rules(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            manifest = root / verification.MANIFEST
            manifest.parent.mkdir(parents=True)
            manifest.write_text(json.dumps({"apis": [{"manual": "docs/spec/api/utility.md#version"}]}))
            required = set(verification.SPEC_LAYOUT_FILES)
            extra = {"docs/spec/api/utility.md", "docs/spec/format/model.md"}
            for name in required | extra:
                target = root / name
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_text("normative fixture\n")
            with patch.object(verification, "ROOT", root), \
                    patch.object(verification, "FIXED_FILES", ()), \
                    patch.object(verification, "FIXED_DIRS", ("docs/spec", "tests/audit")), \
                    patch.object(verification.subprocess, "check_output", return_value="160000 " + "a" * 40 + " 0\tzlib\n"):
                files = verification.source_policy()["files"]
                self.assertTrue(required | extra <= set(files))
                for name in sorted(required):
                    target = root / name
                    target.unlink()
                    with self.subTest(missing=name), self.assertRaisesRegex(verification.Rejected, "protected file missing"):
                        verification.source_policy()
                    target.write_text("normative fixture\n")


if __name__ == "__main__":
    unittest.main()
