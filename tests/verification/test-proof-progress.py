#!/usr/bin/env python3
"""Progress must never promote a draft or disallowed proof to checked status."""
import importlib.util
import json
from pathlib import Path
import re
import tempfile
import unittest
from unittest.mock import patch
from urllib.parse import urljoin, urlsplit

REPO = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location('proof_progress', REPO / 'scripts/proof-progress.py')
progress = importlib.util.module_from_spec(spec)
spec.loader.exec_module(progress)

class ProgressTests(unittest.TestCase):
    def setUp(self):
        self.work = tempfile.TemporaryDirectory()
        self.addCleanup(self.work.cleanup)
        self.root = Path(self.work.name)
        for path in ['tests/audit', 'ZlibF/Proof', 'ZlibF/Spec', 'docs']:
            (self.root / path).mkdir(parents=True)
        self.goals = ['ZlibF.Spec.Public.Goal.' + x for x in 'abcde']
        (self.root / 'tests/audit/goals.txt').write_text('\n'.join(self.goals) + '\n')
        (self.root / 'tests/audit/public-api.json').write_text(json.dumps({'apis': [
            {'goal': g, 'implementation': 'F.' + g[-1], 'manual': 'docs/api.md'} for g in self.goals]}))
        (self.root / 'ZlibF/Spec/Goals.lean').write_text('\n'.join('def Goal.' + x + ' : Prop := True' for x in 'abcde'))
        (self.root / 'ZlibF/Proof/candidate.lean').write_text('theorem candidate : Goal.d := by trivial\n')
        (self.root / 'ZlibF/Proof/exact.lean').write_text('theorem a : Goal.a := by trivial\n')
        (self.root / 'docs/overview.md').write_text('# Status\n\n## Recorded checkpoint\n\nKeep this progress.\n')
        self.export = {'goals': [{'name': g, 'source': 'ZlibF/Spec/Goals.lean', 'description': '', 'proofs': []} for g in self.goals],
                       'declarations': [
                           {'name': 'F.a', 'source': 'ZlibF/Zlib/test.c.lean', 'refs': ['F.helper']},
                           {'name': 'F.helper', 'source': 'ZlibF/Zlib/test.c.lean', 'refs': ['F.b']},
                           {'name': 'F.b', 'source': 'ZlibF/Zlib/test.c.lean', 'refs': ['F.a']},
                           {'name': 'Proof.b', 'source': 'ZlibF/Proof/exact.lean', 'refs': ['Proof.a']}]}
        for i, registered in [(0, True), (1, False)]:
            self.export['goals'][i]['proofs'] = [{'name': 'Proof.' + 'abc'[i], 'source': 'ZlibF/Proof/exact.lean',
                                                 'registered': registered, 'allowedAxioms': True, 'axioms': []}]
        self.addCleanup(patch.stopall)
        patch.object(progress, 'ROOT', self.root).start()
        patch.object(progress.subprocess, 'check_output', return_value='ZlibF/Proof/exact.lean\0').start()

    def graph(self):
        return progress.build_graph(self.export, 'input-fingerprint')

    def test_status_requires_checked_exact_proof_and_allowed_axioms(self):
        states = {n['label']: n['status'] for n in self.graph()['nodes']}
        self.assertEqual(states, dict(zip('abcde', ['registered', 'local', 'open', 'open', 'open'])))
        self.assertIn('Unchecked source:', progress.outputs(self.graph())['docs/progress.md'])

    def test_disallowed_axioms_stop_generation_even_with_an_allowed_proof(self):
        self.export['goals'][0]['proofs'].append({
            'name': 'Proof.invalid', 'source': 'ZlibF/Proof/exact.lean',
            'registered': False, 'allowedAxioms': False, 'axioms': ['Unexpected.assumption']})
        with self.assertRaisesRegex(ValueError, r'disallowed axiom dependencies in Proof.invalid.*Unexpected.assumption'):
            self.graph()

    def test_real_calls_through_helpers_and_cycles_are_preserved(self):
        edges = {(e['from'], e['to'], e['kind']) for e in self.graph()['edges']}
        self.assertIn((self.goals[1], self.goals[0], 'call'), edges)
        self.assertIn((self.goals[0], self.goals[1], 'call'), edges)
        self.assertIn((self.goals[0], self.goals[1], 'proof'), edges)

    def test_missing_registered_goal_rejects_the_snapshot(self):
        self.export['goals'].pop()
        with self.assertRaisesRegex(ValueError, 'complete goal registry'):
            self.graph()

    def test_every_target_is_drawn_and_unrelated_overview_prose_is_preserved(self):
        graph = self.graph()
        output = progress.outputs(graph)
        self.assertEqual(len(re.findall(r'^\s+n\d+\[', progress.mermaid(graph), re.M)), len(self.goals))
        overview = output['docs/overview.md']
        self.assertIn('Keep this progress.', overview)
        (self.root / 'docs/overview.md').write_text(overview.replace('Keep this progress.', 'New independent progress.'))
        updated = progress.outputs(graph)['docs/overview.md']
        self.assertEqual(updated.count(progress.START), 1)
        self.assertIn('New independent progress.', updated)
        self.assertNotIn('progress.html', output['docs/progress.md'])

    def test_three_colour_key_is_outside_diagrams_without_example_nodes(self):
        graph = self.graph()
        self.assertEqual(set(progress.STATUSES), {'registered', 'local', 'open'})
        for diagram in [progress.mermaid(graph), progress.summary_mermaid(graph)]:
            self.assertNotIn('key_', diagram)
            self.assertNotIn('subgraph legend', diagram)
            self.assertNotIn('classDef draft', diagram)
            self.assertNotIn('classDef rejected', diagram)
        for page in progress.outputs(graph).values():
            above_diagram = page.split('```mermaid', 1)[0]
            for symbol in ['🟩', '🟦', '⬜']:
                self.assertIn(symbol, above_diagram)
            self.assertIn('Solid arrows', above_diagram)
            self.assertIn('Dotted arrows', above_diagram)

    def test_all_target_group_and_status_clicks_resolve_to_unique_index_entries(self):
        graph = self.graph()
        output = progress.outputs(graph)
        detail = output['docs/progress.md']
        anchors = re.findall(r'<a id="([^"]+)"></a>', detail)
        self.assertEqual(len(anchors), len(set(anchors)))
        for diagram in [progress.mermaid(graph), progress.summary_mermaid(graph)]:
            links = re.findall(r'click \w+ href "\./progress.md#([^"]+)"', diagram)
            self.assertTrue(links)
            self.assertTrue(set(links) <= set(anchors))
        target_links = re.findall(r'click n\d+ href "\./progress.md#([^"]+)"', progress.mermaid(graph))
        self.assertEqual(len(target_links), len(self.goals))
        self.assertEqual(set(target_links), {progress.target_anchor(n) for n in graph['nodes']})
        groups = {n['group'] for n in graph['nodes']}
        for group in groups:
            self.assertIn(f'](./progress.md#group-{group})', detail)
        self.assertIn('[Contract](../docs/api.md)', detail)
        self.assertIn('Some Markdown viewers disable diagram links', detail)

    def test_diagram_links_keep_the_current_branch_after_a_merge(self):
        graph = self.graph()
        for page, diagram in [('overview.md', progress.summary_mermaid(graph)),
                              ('progress.md', progress.mermaid(graph))]:
            links = re.findall(r'click \w+ href "([^"]+)"', diagram)
            self.assertTrue(links)
            self.assertTrue(all(link.startswith('./progress.md#') for link in links))
            for branch in ['dev', 'main', 'feature/review']:
                base = f'https://github.com/example/project/blob/{branch}/docs/{page}'
                for link in links:
                    resolved = urlsplit(urljoin(base, link))
                    self.assertEqual(resolved.path, f'/example/project/blob/{branch}/docs/progress.md')
                    self.assertTrue(resolved.fragment)

    def test_reference_links_stay_relative_and_keep_source_line_anchors(self):
        graph = self.graph()
        detail = progress.outputs(graph)['docs/progress.md']
        links = re.findall(r'\]\(([^)]+)\)', detail)
        self.assertTrue(all(not urlsplit(link).scheme and not link.startswith('/') for link in links))
        self.assertIn('../ZlibF/Spec/Goals.lean#L1', links)
        self.assertIn('../ZlibF/Proof/exact.lean#L1', links)
        for branch in ['dev', 'main']:
            base = f'https://github.com/example/project/blob/{branch}/docs/progress.md'
            source = urlsplit(urljoin(base, '../ZlibF/Proof/exact.lean#L1'))
            self.assertEqual(source.path, f'/example/project/blob/{branch}/ZlibF/Proof/exact.lean')
            self.assertEqual(source.fragment, 'L1')

    def test_isolation_never_promotes_a_target_to_proved(self):
        graph = self.graph()
        isolated = next(n for n in graph['nodes'] if n['label'] == 'e')
        self.assertFalse(any(isolated['id'] in (e['from'], e['to']) for e in graph['edges']))
        self.assertEqual(isolated['status'], 'open')
        self.assertIn('Why can an isolated node be unfinished?', progress.outputs(graph)['docs/progress.md'])

if __name__ == '__main__':
    unittest.main()
