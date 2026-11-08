#!/usr/bin/env python3
"""Compiler boundaries and exact-proof replay regressions for the public gate."""
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'scripts'))
import verification


class PublicMutationTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='public-mutant-test-')
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        shutil.copyfile(ROOT / 'lean-toolchain', self.root / 'lean-toolchain')
        (self.root / 'lakefile.toml').write_text('name = "ZlibF"\n[[lean_lib]]\nname = "ZlibF"\n')
        (self.root / 'ZlibF/Zlib').mkdir(parents=True)
        self.source = self.root / 'ZlibF/Zlib/fixture.c.lean'
        self.source.write_text('namespace Fixture\ndef target : Nat := 1\nprivate def helper : Nat := 7\nend Fixture\n')
        (self.root / 'ZlibF/Proof.lean').write_text('import ZlibF.Zlib.«fixture.c»\nnamespace Fixture\ndef Goal.checked : Prop := 0 ≤ target\ntheorem exact : Goal.checked := Nat.zero_le target\ntheorem unrelated : target = 1 := rfl\nend Fixture\n')
        (self.root / 'ZlibF.lean').write_text('import ZlibF.Proof\n')
        self.registry = self.root / 'theorems.txt'
        self.registry.write_text('Fixture.exact\n')
        self.build(self.root, 'ZlibF')

    def build(self, root, module):
        result = subprocess.run(['lake', 'build', module], cwd=root, capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def replay(self, root):
        return subprocess.run(['lake', 'env', 'lean', '--run', str(ROOT / 'tests/audit/ReplayPublicProof.lean'),
            str(self.root / '.lake/build/lib/lean'), str(root / '.lake/build/lib/lean'),
            'ZlibF.Zlib.«fixture.c»', 'Fixture.Goal.checked', str(self.registry)],
            cwd=self.root, capture_output=True, text=True)

    def test_native_parser_matches_interpreter_and_ignores_candidate_imports(self):
        self.source.write_text('import CandidateMustNotExecute\nnamespace Fixture\n'
                               'def target (n : Nat := 1) : Nat := n + 1\nend Fixture\n')
        env = dict(os.environ)
        env.pop('LEAN_PATH', None)
        env.pop('LEAN_SRC_PATH', None)
        env['ELAN_TOOLCHAIN'] = (ROOT / 'lean-toolchain').read_text().strip()
        lean = subprocess.check_output(['elan', 'which', 'lean'], cwd=ROOT, env=env, text=True).strip()
        with tempfile.TemporaryDirectory(prefix='reference-parser-') as directory:
            reference = subprocess.run(
                [lean, '--run', str(ROOT / 'tests/audit/DeclarationSpan.lean'), str(self.source)],
                cwd=directory, env=env, capture_output=True, text=True)
        self.assertEqual(reference.returncode, 0, reference.stdout + reference.stderr)
        with patch.dict(os.environ, {'LEAN_PATH': str(self.root), 'LEAN_SRC_PATH': str(self.root)}):
            native = verification.mutation_spans.parse(self.source)
        self.assertEqual(native, json.loads(reference.stdout))
        self.assertFalse(native['sourceImportsExecuted'])

    def test_private_sibling_is_outside_parsed_body(self):
        parsed = verification.mutation_spans.parse(self.source)
        command = verification.mutation_spans.unique(parsed, 'target')
        span = command['span']
        data = self.source.read_bytes()
        self.assertLessEqual(span[1], data.index(b'private def helper'))
        start, end = command['declaration']['body']
        self.assertEqual(data[start:end], b'1')
        directory = self.root / 'tests/audit'
        directory.mkdir(parents=True)
        lists = self.root / 'tests/proof-mutants'
        lists.mkdir(parents=True)
        (lists / 'fixture.tsv').write_text('sibling\tZlibF/Zlib/fixture.c.lean\tprivate def helper : Nat := 7\tprivate def helper : Nat := 8\tProof\n')
        (directory / 'public-mutants.json').write_text(json.dumps({'version': 1, 'targets': {
            'Fixture.Goal.checked': [{'list': 'tests/proof-mutants/fixture.tsv', 'name': 'sibling'}]}}))
        manifest = {'apis': [{'goal': 'Fixture.Goal.checked', 'function': 'target',
            'implementation': 'Fixture.target', 'source': 'ZlibF/Zlib/fixture.c.lean', 'scope': 'lp64-linux'}]}
        with patch.object(verification, 'ROOT', self.root):
            # The old sibling regex accepts this. The compiler boundary must reject it.
            verification.public_mutants(manifest)
            with self.assertRaisesRegex(verification.Rejected, 'parsed function body'):
                verification.check_public_mutant_spans(manifest)

    def test_injected_command_and_binder_default_reject(self):
        self.source.write_text('import Does.Not.Exist\nnamespace Fixture\ndef target (x : Nat := 1) : Nat := x + 1\nend Fixture\n')
        mutant = self.root / 'mutant.lean'
        for old, new in [('x + 1', 'x + 2\ndef injected : Nat := 0'),
                         ('x : Nat := 1', 'x : Nat := 2')]:
            mutant.write_text(self.source.read_text().replace(old, new))
            with self.assertRaises(ValueError):
                verification.mutation_spans.check(self.source, mutant, 'target')
        mutant.write_text(self.source.read_text().replace('x + 1', 'x + 2'))
        self.assertTrue(verification.mutation_spans.check(self.source, mutant, 'target')['accepted'])
        self.source.write_text('/-- Unicode α. -/\n@[simp] private def target (s : String := "α") : String := s ++ "β"\n')
        mutant.write_text(self.source.read_text().replace('s ++ "β"', 's ++ "λμβ"'))
        self.assertTrue(verification.mutation_spans.check(self.source, mutant, 'target')['accepted'])
        self.source.write_bytes(self.source.read_bytes().replace(b'\n', b'\r\n'))
        with self.assertRaisesRegex(ValueError, 'CR line endings'):
            verification.mutation_spans.parse(self.source)
        self.source.write_text('set_option maxRecDepth 100 in\ndef target : Nat := 1\n')
        mutant.write_text(self.source.read_text().replace('Nat := 1', 'Nat := 2'))
        with self.assertRaises(ValueError):
            verification.mutation_spans.check(self.source, mutant, 'target')

    def test_unrelated_failed_theorem_cannot_kill_exact_proof(self):
        original = self.replay(self.root)
        self.assertEqual(original.returncode, 0, original.stdout + original.stderr)
        candidate = self.root / 'candidate'
        shutil.copytree(self.root, candidate, ignore=shutil.ignore_patterns('candidate'))
        path = candidate / 'ZlibF/Zlib/fixture.c.lean'
        path.write_text(path.read_text().replace('target : Nat := 1', 'target : Nat := 2'))
        self.build(candidate, 'ZlibF.Zlib.«fixture.c»')
        changed = self.replay(candidate)
        self.assertEqual(changed.returncode, 0, changed.stdout + changed.stderr)
        failed = subprocess.run(['lake', 'build', 'ZlibF'], cwd=candidate, capture_output=True, text=True)
        self.assertNotEqual(failed.returncode, 0)
        self.assertIn('unrelated', (candidate / 'ZlibF/Proof.lean').read_text())

    def test_exact_proof_rejects_actual_result_change(self):
        proof = self.root / 'ZlibF/Proof.lean'
        proof.write_text('import ZlibF.Zlib.«fixture.c»\nnamespace Fixture\ndef Goal.checked : Prop := target = 1\ntheorem exact : Goal.checked := rfl\nend Fixture\n')
        self.build(self.root, 'ZlibF')
        self.assertEqual(self.replay(self.root).returncode, 0)
        candidate = self.root / 'candidate'
        shutil.copytree(self.root, candidate, ignore=shutil.ignore_patterns('candidate'))
        path = candidate / 'ZlibF/Zlib/fixture.c.lean'
        path.write_text(path.read_text().replace('target : Nat := 1', 'target : Nat := 2'))
        self.build(candidate, 'ZlibF.Zlib.«fixture.c»')
        changed = self.replay(candidate)
        self.assertEqual(changed.returncode, 2, changed.stdout + changed.stderr)
        self.assertTrue(changed.stdout.startswith('EXACT_PROOF_REJECTED: '))


if __name__ == '__main__':
    unittest.main()
