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
                    "apis": [{"function": "documented", "functional_goal": "Goal.documented",
                              "safety_goal": "Goal.documented_safety", "scope": "lp64-linux"},
                             {"function": "hidden", "functional_goal": "Goal.hidden", "safety_goal": None,
                              "scope": "lp64-linux"}],
                    "safety_goals": ["Goal.documented_safety", "Goal.sequence_safety"],
                    "nonvacuity_goals": ["Goal.domain"], "sequence_goals": ["Goal.sequence"]}
        # The safety goals are required; the functional goals and the sequence goals are not.
        self.assertEqual(verification.required_public_goals(manifest),
                         ["Goal.documented_safety", "Goal.sequence_safety", "Goal.domain"])
        self.assertEqual(verification.functional_goals(manifest),
                         ["Goal.documented", "Goal.hidden", "Goal.sequence"])

    def open_manifest(self, *open_goals):
        return {"apis": [{"function": "first", "functional_goal": "Goal.first",
                          "safety_goal": "Goal.first_safety", "scope": "lp64-linux"}],
                "safety_goals": ["Goal.first_safety", "Goal.second_safety"], "nonvacuity_goals": [],
                "open_safety": [{"goal": g, "owner": "someone"} for g in open_goals]}

    def test_open_safety_names_required_goals_with_owners(self):
        verification.check_open_safety(self.open_manifest("Goal.second_safety"))
        with self.assertRaises(verification.Rejected):
            verification.check_open_safety(self.open_manifest("Goal.first"))
        with self.assertRaises(verification.Rejected):
            verification.check_open_safety(self.open_manifest("Goal.second_safety", "Goal.second_safety"))
        manifest = self.open_manifest()
        manifest["open_safety"] = [{"goal": "Goal.second_safety", "owner": " "}]
        with self.assertRaises(verification.Rejected):
            verification.check_open_safety(manifest)

    def test_required_goals_are_proved_unless_open(self):
        # Decided on proved-goals.txt (which the auditor checks to be exact), never on report text.
        (self.root / "tests/audit").mkdir(parents=True, exist_ok=True)
        (self.root / "tests/audit/proved-goals.txt").write_text("Goal.first_safety\n")
        with patch.object(verification, "ROOT", self.root):
            verification.check_required_proved(self.open_manifest("Goal.second_safety"))
            with self.assertRaises(verification.Rejected):
                verification.check_required_proved(self.open_manifest())
            with self.assertRaises(verification.Rejected):
                verification.check_required_proved(self.open_manifest("Goal.first_safety", "Goal.second_safety"))

    def test_open_safety_floor_when_the_base_has_no_open_list(self):
        repo = self.root / "repo"
        (repo / "tests/audit").mkdir(parents=True)
        def git(*args):
            subprocess.run(["git", "-c", "user.name=t", "-c", "user.email=t@t", *args], cwd=repo, check=True,
                           stdout=subprocess.DEVNULL)
        git("init", "-q")
        manifest = repo / "tests/audit/public-api.json"
        manifest.write_text(json.dumps(self.open_manifest("Goal.second_safety")))
        git("add", "-A"); git("commit", "-qm", "floor"); git("tag", "floor")
        old = self.open_manifest(); del old["open_safety"]
        manifest.write_text(json.dumps(old))
        git("add", "-A"); git("commit", "-qm", "old base"); git("tag", "base")
        with patch.object(verification, "ROOT", repo), patch.object(verification, "OPEN_SAFETY_FLOOR", "floor"), \
                patch.dict(os.environ, {"ZLIBF_BASE_REF": "base"}):
            verification.check_open_safety_shrinks(self.open_manifest("Goal.second_safety"))
            with self.assertRaisesRegex(verification.Rejected, "first_safety"):
                verification.check_open_safety_shrinks(self.open_manifest("Goal.first_safety", "Goal.second_safety"))

    def test_registered_theorems_and_proved_goals_only_shrink_with_a_reviewed_entry(self):
        repo = self.root / "repo"
        audit = repo / "tests/audit"
        audit.mkdir(parents=True)
        def git(*args):
            subprocess.run(["git", "-c", "user.name=t", "-c", "user.email=t@t", *args], cwd=repo, check=True,
                           stdout=subprocess.DEVNULL)
        git("init", "-q")
        (audit / "theorems.txt").write_text("T.a\nT.b\n")
        (audit / "proved-goals.txt").write_text("Goal.a\nGoal.b\n")
        git("add", "-A"); git("commit", "-qm", "base"); git("tag", "base")
        (repo / "README").write_text("x\n")
        git("add", "README"); git("commit", "-qm", "head")
        with patch.object(verification, "ROOT", repo), patch.dict(os.environ, {"ZLIBF_BASE_REF": "base"}):
            (audit / "theorems.txt").write_text("T.a\nT.b\nT.c\n")
            (audit / "proved-goals.txt").write_text("Goal.a\nGoal.b\nGoal.c\n")
            verification.check_registries_shrink()
            (audit / "theorems.txt").write_text("T.a\n")
            with self.assertRaisesRegex(verification.Rejected, "T.b"):
                verification.check_registries_shrink()
            (audit / "registry-removals.json").write_text(json.dumps({"version": 1, "proved_goals": [],
                "theorems": [{"name": "T.b", "reason": "merged into T.a"}]}))
            verification.check_registries_shrink()
            (audit / "proved-goals.txt").write_text("Goal.a\n")
            with self.assertRaisesRegex(verification.Rejected, "Goal.b"):
                verification.check_registries_shrink()
            (audit / "registry-removals.json").write_text(json.dumps({"version": 1, "theorems": [
                {"name": "T.b", "reason": ""}], "proved_goals": []}))
            with self.assertRaises(verification.Rejected):
                verification.check_registries_shrink()

    def test_open_safety_only_shrinks_against_the_base_branch(self):
        repo = self.root / "repo"
        (repo / "tests/audit").mkdir(parents=True)
        def git(*args):
            subprocess.run(["git", "-c", "user.name=t", "-c", "user.email=t@t", *args], cwd=repo, check=True,
                           stdout=subprocess.DEVNULL)
        git("init", "-q")
        (repo / "tests/audit/public-api.json").write_text(json.dumps(self.open_manifest("Goal.second_safety")))
        git("add", "-A"); git("commit", "-qm", "base"); git("tag", "base")
        (repo / "README").write_text("x\n")
        git("add", "README"); git("commit", "-qm", "head")
        with patch.object(verification, "ROOT", repo), patch.dict(os.environ, {"ZLIBF_BASE_REF": "base"}):
            verification.check_open_safety_shrinks(self.open_manifest("Goal.second_safety"))
            verification.check_open_safety_shrinks(self.open_manifest())
            grown = self.open_manifest("Goal.second_safety")
            grown["safety_goals"].append("Goal.third_safety")
            grown["open_safety"].append({"goal": "Goal.third_safety", "owner": "someone"})
            verification.check_open_safety_shrinks(grown)
            with self.assertRaisesRegex(verification.Rejected, "first_safety"):
                verification.check_open_safety_shrinks(self.open_manifest("Goal.first_safety", "Goal.second_safety"))
        with patch.object(verification, "ROOT", repo), patch.dict(os.environ, {"ZLIBF_BASE_REF": "missing"}):
            with self.assertRaises(verification.Rejected):
                verification.check_open_safety_shrinks(self.open_manifest())

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
        manifest = {"apis": [{"functional_goal": "Goal.first", "safety_goal": "Goal.first_safe",
                              "function": "first", "source": source, "scope": "lp64-linux"}]}
        def write_targets(targets):
            mapping.write_text(json.dumps({"version": 1, "targets": targets}))
        reference = {"list": "tests/proof-mutants/fixture.tsv", "name": "first-change"}
        with patch.object(verification, "ROOT", self.root), \
                patch.object(verification, "MUTANT_COVERAGE_PENDING", {}):
            write_targets({})
            verification.check_public_mutant_coverage(manifest, set())
            with self.assertRaises(verification.Rejected):
                verification.check_public_mutant_coverage(manifest, {"Goal.first"})
            # A proved per-function safety goal needs mutants of its own too (F2).
            with self.assertRaisesRegex(verification.Rejected, "first_safe"):
                verification.check_public_mutant_coverage(manifest, {"Goal.first_safe"})
            with patch.object(verification, "MUTANT_COVERAGE_PENDING", {"Goal.first_safe": "pending rows"}):
                verification.check_public_mutant_coverage(manifest, {"Goal.first_safe"})
                with self.assertRaisesRegex(verification.Rejected, "stale"):
                    verification.check_public_mutant_coverage(manifest, set())
            write_targets({"Goal.first": [reference]})
            verification.check_public_mutant_coverage(manifest, {"Goal.first"})
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
                verification.check_public_mutant_coverage(manifest, {"Goal.first"})
            write_targets({"Goal.first": [reference]})
            original = table.read_text()
            write_targets({"Goal.first": [dict(reference, name="")]})
            table.write_text(original.replace("first-change", "", 1))
            with self.assertRaises(verification.Rejected):
                verification.check_public_mutant_coverage(manifest, {"Goal.first"})
            write_targets({"Goal.first": [reference]})
            table.write_text(original.replace("def first : Nat := 1", "def renamed : Nat := 1"))
            with self.assertRaises(verification.Rejected):
                verification.check_public_mutant_coverage(manifest, {"Goal.first"})
            table.write_text(original.replace("\tFixture\n", "\tFixture\tgap:missing proof\n", 1))
            with self.assertRaises(verification.Rejected):
                verification.check_public_mutant_coverage(manifest, {"Goal.first"})
            table.write_text(original.replace(source, "ZlibF/Spec/Fixture.lean", 1))
            with self.assertRaises(verification.Rejected):
                verification.check_public_mutant_coverage(manifest, {"Goal.first"})
            # the function's own safety goal keys the same function; another name does not
            table.write_text(original)
            write_targets({"Goal.first_safe": [reference]})
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

    def audit(self, strict=False, compare=True, proved=None):
        args = ["lake", "env", str(self.auditor),
                str(self.theorems), str(self.goals), str(ROOT / "tests/audit/compiler-helpers.txt")]
        if proved is not None:
            path = self.root / "proved-goals.txt"
            path.write_text("".join(name + "\n" for name in proved))
            args += ["--proved", str(path)]
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

    def test_proved_list_is_exact(self):
        exact = self.audit(proved=["ZlibF.Fixture.Goal.checked"])
        self.assertEqual(exact.returncode, 0, exact.stdout + exact.stderr)
        unrecorded = self.audit(proved=[])
        self.assertNotEqual(unrecorded.returncode, 0)
        self.assertIn("is not recorded", unrecorded.stderr)
        self.theorems.write_text("ZlibF.Fixture.stronger\n")
        forged = self.audit(proved=["ZlibF.Fixture.Goal.checked"])
        self.assertNotEqual(forged.returncode, 0)
        self.assertIn("recorded proved goal ZlibF.Fixture.Goal.checked is OPEN", forged.stderr)

    def test_control_character_in_a_name_is_rejected(self):
        # A newline inside a quoted name would print a forged report line (F1).
        self.theorems.write_text("ZlibF.Fixture.stronger\n")
        self.source.write_text(FIXTURE + "\nnamespace ZlibF.Fixture\ndef «x\ngoal ZlibF.Fixture.Goal.checked "
                               "PROVED by y» : Nat := 1\nend ZlibF.Fixture\n")
        self.build()
        result = self.audit(compare=False)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("control character", result.stderr)
        self.assertNotIn("PROVED", result.stdout)

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
