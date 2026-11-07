#!/usr/bin/env python3
"""Progress must never promote a draft or disallowed proof to checked status."""
import importlib.util
import json
import os
import shutil
import subprocess
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
        (self.root / 'docs/overview.md').write_text('# Proof narrative\n\nA stable explanation.\n')
        (self.root / 'docs/progress.md').write_text('# Status\n\n## Recorded checkpoint\n\nKeep this progress.\n')
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
        self.link_context = {'repository': 'https://github.com/example/project', 'revision': 'a' * 40,
                             'files': ['docs/progress.md', 'ZlibF/Spec/Goals.lean'],
                             'progressAnchors': ['group-buffers', *[progress.target_anchor({'id': g}) for g in self.goals]],
                             'progressHeadings': ['address-model']}
        patch.object(progress, 'link_context', return_value=self.link_context).start()

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

    def test_every_target_is_drawn_and_maintained_progress_prose_is_preserved(self):
        graph = self.graph()
        output = progress.outputs(graph)
        self.assertEqual(len(re.findall(r'^\s+n\d+\[', progress.mermaid(graph), re.M)), len(self.goals))
        overview = output['docs/progress.md']
        self.assertIn('Keep this progress.', overview)
        (self.root / 'docs/progress.md').write_text(overview.replace('Keep this progress.', 'New independent progress.'))
        updated = progress.outputs(graph)['docs/progress.md']
        self.assertEqual(updated.count(progress.START), 1)
        self.assertIn('New independent progress.', updated)
        self.assertNotIn('progress.html', output['docs/progress.md'])
        self.assertNotIn('docs/overview.md', output)
        self.assertEqual((self.root / 'docs/overview.md').read_text(), '# Proof narrative\n\nA stable explanation.\n')

    def test_colour_key_is_outside_diagrams_without_example_nodes(self):
        graph = self.graph()
        self.assertEqual(set(progress.COVERAGE), {'unproved', 'default', 'common', 'all'})
        diagram = progress.mermaid(graph)
        self.assertNotIn('key_', diagram)
        self.assertNotIn('subgraph legend', diagram)
        output = progress.outputs(graph)
        self.assertEqual(sum(page.count('```mermaid') for page in output.values()), 1)
        above = output['docs/progress.md'].split('```mermaid', 1)[0]
        for symbol in ['⬜', '🟦', '🟨', '🟩']: self.assertIn(symbol, above)
        self.assertIn('Solid arrows show actual proof reuse', above)

    def add_blocker(self, *goals):
        path = self.root / 'docs/progress.md'
        markers = ''.join(f'<!-- proof-blocker: {goal} -->\n' for goal in goals)
        path.write_text(path.read_text() + '\n### Address model\n' + markers + '\nEvidence and next step.\n')

    def test_documented_blockers_are_red_and_link_directly_to_the_reason(self):
        self.add_blocker(self.goals[2], self.goals[3])
        self.export['declarations'][0]['refs'].append('F.c')
        graph = self.graph()
        self.assertEqual(graph['counts'], {'registered': 1, 'local': 1, 'blocked': 2, 'open': 1})
        self.assertEqual(sum(graph['counts'].values()), len(self.goals))
        diagram = progress.mermaid(graph)
        for index in [2, 3]:
            self.assertIn(f'n{index}["{"abcde"[index]}<br/>Blocked"]:::unproved', diagram)
            self.assertIn(f'click n{index} href "https://github.com/example/project/blob/{"a" * 40}/docs/progress.md#address-model"', diagram)
        for branch in ['dev', 'main']:
            base = f'https://github.com/example/project/blob/{branch}/docs/progress.md'
            url = urlsplit(urljoin(base, progress.target_url(graph, graph['nodes'][2])))
            self.assertEqual(url.path, f'/example/project/blob/{"a" * 40}/docs/progress.md')
            self.assertEqual(url.fragment, 'address-model')
        self.assertIn('(./progress.md#address-model)', progress.blocker_index(graph))
        self.assertNotIn('overview.md#', progress.blocker_index(graph))
        self.assertIn('class n2 obstacle', diagram)
        self.assertIn('class n3 obstacle', diagram)
        for path, content in progress.outputs(graph).items():
            if path == 'docs/supporting-proofs.md': continue
            self.assertIn('progress.md#address-model)', content)
        self.assertEqual(next(n for n in graph['nodes'] if n['label'] == 'e')['status'], 'open')
        self.assertEqual(next(n for n in graph['nodes'] if n['label'] == 'a')['status'], 'registered')

    def test_blocker_cannot_override_a_checked_proof(self):
        self.add_blocker(self.goals[0])
        with self.assertRaisesRegex(ValueError, 'stale blocker for checked target'):
            self.graph()

    def test_unknown_and_duplicate_blocker_targets_are_rejected(self):
        self.add_blocker('ZlibF.Spec.Public.Goal.unknown')
        with self.assertRaisesRegex(ValueError, 'unregistered targets'):
            self.graph()
        self.add_blocker(self.goals[2], self.goals[2])
        with self.assertRaisesRegex(ValueError, 'duplicate proof blocker'):
            self.graph()

    def test_blocker_metadata_changes_the_snapshot_but_rendering_does_not(self):
        (self.root / 'ZlibF.lean').write_text('')
        (self.root / 'tests/audit/theorems.txt').write_text('Proof.a\n')
        before = progress.fingerprint()
        self.add_blocker(self.goals[2])
        after = progress.fingerprint()
        self.assertNotEqual(before, after)
        output = progress.outputs(self.graph())
        (self.root / 'docs/progress.md').write_text(output['docs/progress.md'])
        self.assertEqual(progress.fingerprint(), after)

    def test_all_target_group_and_status_clicks_resolve_to_unique_index_entries(self):
        graph = self.graph()
        output = progress.outputs(graph)
        detail = output['docs/progress.md']
        anchors = re.findall(r'<a id="([^"]+)"></a>', detail)
        self.assertEqual(len(anchors), len(set(anchors)))
        for node in graph['nodes']:
            self.assertIn(progress.target_anchor(node), anchors)
            url = urlsplit(progress.target_url(graph, node))
            self.assertEqual(url.path, f'/example/project/blob/{"a" * 40}/ZlibF/Spec/Goals.lean')
            self.assertEqual(url.fragment, f'L{node["line"]}')
        # Diagram destinations must not return to the old mixed-scope graph.
        for diagram in [progress.mermaid(graph)]:
            self.assertNotIn('/docs/progress.md#', diagram)
        groups = {n['group'] for n in graph['nodes']}
        for group in groups:
            self.assertIn(f'id="group-{group}"', detail)
        self.assertIn('[Contract](../docs/api.md)', detail)
        self.assertIn('Some Markdown viewers disable diagram links', detail)

    def test_diagram_links_escape_github_iframe_and_survive_branch_changes(self):
        graph = self.graph()
        for page, diagram in [('overview.md', progress.mermaid(graph))]:
            links = re.findall(r'click \w+ href "([^"]+)"', diagram)
            self.assertTrue(links)
            self.assertTrue(all(line.endswith('_blank') for line in diagram.splitlines() if line.strip().startswith('click ')))
            self.assertTrue(all(link.startswith('https://github.com/example/project/blob/' + 'a' * 40) for link in links))
            bases = ['https://viewscreen.githubusercontent.com/markdown/mermaid',
                     'https://github.com/example/project/blob/dev/docs/' + page,
                     'https://github.com/example/project/blob/main/docs/' + page]
            for base in bases:
                for link in links:
                    resolved = urlsplit(urljoin(base, link))
                    self.assertEqual(resolved.netloc, 'github.com')
                    self.assertEqual(resolved.path, f'/example/project/blob/{"a" * 40}/ZlibF/Spec/Goals.lean')

    def test_new_targets_and_groups_link_to_existing_specifications(self):
        self.link_context['progressAnchors'] = []
        graph = self.graph()
        self.assertEqual(progress.target_url(graph, graph['nodes'][0]),
                         f'https://github.com/example/project/blob/{"a" * 40}/ZlibF/Spec/Goals.lean#L1')
        self.assertEqual(progress.group_url(graph, 'buffers'),
                         f'https://github.com/example/project/blob/{"a" * 40}/ZlibF/Spec/Goals.lean')
        self.link_context['files'].remove('ZlibF/Spec/Goals.lean')
        with self.assertRaisesRegex(ValueError, 'before generating'):
            progress.target_url(graph, graph['nodes'][0])

    def test_recorded_revision_is_stable_until_proof_inputs_change(self):
        (self.root / 'docs/progress.md').write_text(
            '<!-- proof-link-revision: ' + 'a' * 40 + ' -->\nInput fingerprint: `123abc`.\n')
        self.assertEqual(progress.recorded_link_revision('123abc'), 'a' * 40)
        self.assertIsNone(progress.recorded_link_revision('456def'))

    def test_github_remote_formats(self):
        for remote in ['git@github.com:example/project.git', 'ssh://git@github.com/example/project.git',
                       'https://github.com/example/project.git']:
            self.assertEqual(progress.github_repository(remote), 'https://github.com/example/project')
        with self.assertRaisesRegex(ValueError, 'GitHub repository'):
            progress.github_repository('https://elsewhere.invalid/project.git')

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

    def test_internal_goals_keep_the_address_group_and_do_not_become_buffer_apis(self):
        self.assertEqual(progress.group('C.ByteAddress.Spec.Goal.pointerAddress'), 'addresses')
        self.assertEqual(progress.group('Zlib.Inffast.Spec.Goal.step_safe'), 'fast')
        self.assertEqual(progress.group('ZlibF.Math.LZ77Copy.Goal.output_copy_refines_lz77'), 'copy')
        self.assertEqual(progress.group('ZlibF.Spec.Public.Goal.compress'), 'buffers')

    def add_support(self):
        goal = 'ZlibF.Math.Example.Goal.helper'
        self.goals.append(goal)
        (self.root / 'tests/audit/goals.txt').write_text('\n'.join(self.goals) + '\n')
        self.export['goals'].append({'name': goal, 'source': 'ZlibF/Spec/Goals.lean',
                                    'description': '', 'proofs': []})
        return goal

    def test_public_and_supporting_views_partition_registry_without_inflating_counts(self):
        support = self.add_support()
        self.export['declarations'].append({'name': support, 'source': 'ZlibF/Spec/Goals.lean',
                                             'refs': [self.goals[0]]})
        graph = self.graph()
        public = progress.select_view(graph, 'public')
        supporting = progress.select_view(graph, 'supporting')
        pids = {n['id'] for n in public['nodes']}
        sids = {n['id'] for n in supporting['nodes']}
        self.assertEqual(pids | sids, set(self.goals))
        self.assertFalse(pids & sids)
        self.assertEqual(sum(public['counts'].values()), 5)
        self.assertEqual(supporting['counts'], {'open': 1})
        for view, ids in [(public, pids), (supporting, sids)]:
            self.assertTrue(all(e['from'] in ids and e['to'] in ids for e in view['edges']))
        output = progress.outputs(graph)
        self.assertIn(progress.target_anchor({'id': support}), output['docs/progress.md'])
        self.assertIn('Internal proof obligations', output['docs/progress.md'])
        self.assertNotIn('docs/supporting-proofs.md', output)
        self.assertIn('**6 fixed targets**', output['docs/progress.md'])
        self.assertNotIn('docs/supporting-proofs.md', output)

    def test_supporting_module_dependencies_include_types_and_compress_helpers(self):
        self.add_support()
        self.export['goals'][-1]['proofs'] = [{'name': 'Support.proof', 'source': 'ZlibF/Proof/exact.lean',
            'registered': False, 'allowedAxioms': True, 'axioms': []}]
        self.export['declarations'] += [
            {'name': 'Support.proof', 'source': 'ZlibF/Proof/exact.lean', 'refs': ['Intermediate.lemma']},
            {'name': 'Intermediate.lemma', 'source': 'ZlibF/Math/Helper.lean', 'refs': [], 'typeRefs': ['Support.goal']},
            {'name': 'Support.goal', 'source': 'ZlibF/Spec/Goals.lean', 'refs': []}]
        graph = self.graph()
        self.assertIn(('ZlibF/Spec/Goals.lean', 'ZlibF/Proof/exact.lean'), graph['modules']['edges'])
        self.assertNotIn('ZlibF/Math/Helper.lean', graph['modules']['nodes'])
        self.link_context['files'].append('ZlibF/Proof/exact.lean')
        output = progress.outputs(graph)
        self.assertEqual(set(output), {'docs/progress.md'})
        self.assertIn('**6 fixed targets: 5 public and 1 supporting.**', output['docs/progress.md'])

    def test_manifest_scope_is_complete_and_cannot_silently_drop_a_public_goal(self):
        path = self.root / 'tests/audit/public-api.json'
        manifest = json.loads(path.read_text())
        manifest['apis'].pop()
        path.write_text(json.dumps(manifest))
        with self.assertRaisesRegex(ValueError, 'public goal missing'):
            self.graph()
        manifest['sequence_goals'] = [self.goals[-1]]
        path.write_text(json.dumps(manifest))
        self.assertEqual(len(progress.select_view(self.graph(), 'public')['nodes']), 5)
        manifest['nonvacuity_goals'] = ['ZlibF.Spec.Public.Goal.absent']
        path.write_text(json.dumps(manifest))
        with self.assertRaisesRegex(ValueError, 'targets missing'):
            self.graph()

    def add_readiness(self, targets='`c`, `d`', label='Needs: position history'):
        path = self.root / 'docs/progress.md'
        path.write_text(path.read_text() +
            '\n### Public API proof readiness\n\n<!-- proof-readiness:start -->\n' +
            '| Public targets | Proof work shown in graph | Next work and missing prerequisite |\n' +
            '| --- | --- | --- |\n' + f'| {targets} | {label} | Derive the invariant from actual histories. |\n' +
            '<!-- proof-readiness:end -->\n')

    def test_readiness_never_grants_checked_status_or_adds_targets_and_edges(self):
        before = self.graph()
        self.add_readiness(label='Start: open and cleanup')
        after = self.graph()
        self.assertEqual(before['counts'], after['counts'])
        self.assertEqual(before['edges'], after['edges'])
        self.assertEqual(len(before['nodes']), len(after['nodes']))
        node = next(n for n in after['nodes'] if n['label'] == 'c')
        self.assertEqual(node['status'], 'open')
        self.assertEqual(node['readiness']['label'], 'Start: open and cleanup')
        self.assertEqual(progress.coverage_level(node), 'unproved')
        page = progress.outputs(after)['docs/progress.md']
        self.assertIn('[Start: open and cleanup](progress.md#public-api-proof-readiness)', page)

    def test_missing_readiness_is_explicitly_unreviewed(self):
        graph = progress.select_view(self.graph(), 'public')
        self.assertIn('Prerequisites unreviewed', progress.outputs(graph)['docs/progress.md'])
        self.assertNotIn('Start:', progress.mermaid(graph))

    def test_readiness_rejects_duplicate_unknown_and_malformed_entries(self):
        self.add_readiness(targets='`absent`')
        with self.assertRaisesRegex(ValueError, 'unregistered targets'):
            self.graph()
        path = self.root / 'docs/progress.md'
        text = path.read_text().replace('`absent`', '`c`, `c`')
        path.write_text(text)
        with self.assertRaisesRegex(ValueError, 'duplicate proof readiness'):
            self.graph()
        path.write_text(text.replace('`c`, `c`', '`c`').replace('Needs: position history', 'Registered: all done'))
        with self.assertRaisesRegex(ValueError, 'invalid proof readiness label'):
            self.graph()

    def test_readiness_links_open_the_specific_family_row(self):
        self.add_readiness()
        path = self.root / 'docs/progress.md'
        path.write_text(path.read_text().replace('Derive the invariant',
            '<a id="readiness-position"></a> Derive the invariant'))
        graph = self.graph()
        for name in ['c', 'd']:
            node = next(n for n in graph['nodes'] if n['label'] == name)
            self.assertEqual(node['readiness']['anchor'], 'readiness-position')
        self.assertIn('(progress.md#readiness-position)', progress.outputs(graph)['docs/progress.md'])

    def test_next_work_column_is_only_in_the_public_view(self):
        output = progress.outputs(self.graph())
        self.assertIn('Reviewed next work', output['docs/progress.md'])
        self.assertEqual(set(output), {'docs/progress.md'})

    def test_readiness_cannot_create_a_blocker(self):
        self.add_readiness(targets='`c`', label='Blocked: no evidence')
        with self.assertRaisesRegex(ValueError, 'cannot establish a blocker'):
            self.graph()

    def test_readiness_changes_fingerprint_and_generated_progress_preserves_the_table(self):
        (self.root / 'ZlibF.lean').write_text('')
        (self.root / 'tests/audit/theorems.txt').write_text('Proof.a\n')
        before = progress.fingerprint()
        self.add_readiness()
        self.assertNotEqual(before, progress.fingerprint())
        text = progress.outputs(self.graph())['docs/progress.md']
        self.assertIn('<!-- proof-readiness:start -->', text)
        self.assertIn('Needs: position history', text)

    def test_overview_cannot_supply_status_or_change_the_progress_fingerprint(self):
        (self.root / 'ZlibF.lean').write_text('')
        (self.root / 'tests/audit/theorems.txt').write_text('Proof.a\n')
        before = progress.fingerprint()
        (self.root / 'docs/overview.md').write_text(
            '# Proof narrative\n\n## A narrative section\n'
            '<!-- proof-blocker: ZlibF.Spec.Public.Goal.unknown -->\n')
        self.assertEqual(progress.fingerprint(), before)
        self.assertEqual(self.graph()['counts'], {'registered': 1, 'local': 1, 'open': 3})
        self.assertEqual(set(progress.outputs(self.graph())), {'docs/progress.md'})

    def test_malformed_progress_envelope_is_rejected_without_overwriting_manual_text(self):
        path = self.root / 'docs/progress.md'
        for text in [progress.START, progress.END, progress.START + progress.START + progress.END]:
            path.write_text(text + '\nKeep this work inventory.\n')
            with self.subTest(text=text), self.assertRaisesRegex(ValueError, 'invalid progress markers'):
                progress.outputs(self.graph())
            self.assertIn('Keep this work inventory.', path.read_text())

    def test_call_cycles_do_not_become_proof_dependencies_in_the_single_graph(self):
        graph = self.graph()
        diagram = progress.mermaid(graph)
        self.assertIn('n0 --> n1', diagram)
        self.assertNotIn('n1 --> n0', diagram)
        self.assertIn('n1 -.-> n0', diagram)
        page = progress.outputs(graph)['docs/progress.md']
        for title in ['Observed proof dependencies', 'C function calls', 'Specification references']:
            self.assertIn('## ' + title, page)

    def test_source_metadata_and_partial_lemmas_cannot_grant_configuration_coverage(self):
        node = self.graph()['nodes'][2]
        for key in ['default', 'common', 'all']:
            node['coverage'] = key
            self.assertEqual(progress.coverage_level(node), 'unproved')
        self.assertEqual(progress.coverage_level(self.graph()['nodes'][1]), 'all')
        self.assertEqual(self.graph()['nodes'][1]['status'], 'local')

    def test_every_fixed_target_is_present_once_in_progress(self):
        self.add_support()
        graph = self.graph()
        output = progress.outputs(graph)
        diagram = output['docs/progress.md'].split('```mermaid',1)[1].split('```',1)[0]
        self.assertEqual(len(re.findall(r'^\s+n\d+\[', diagram, re.M)), len(self.goals))
        self.assertEqual(output['docs/progress.md'].count('```mermaid'), 1)
        self.assertEqual(set(output), {'docs/progress.md'})

    def test_registered_auxiliary_theorems_are_indexed_without_becoming_targets(self):
        self.export['declarations'] += [
            {'name':'Proof.a', 'source':'ZlibF/Proof/exact.lean', 'refs':['Helper.checked']},
            {'name':'Helper.checked', 'source':'ZlibF/Proof/exact.lean', 'refs':[], 'theorem':True, 'registered':True},
            {'name':'Helper.witness', 'source':'ZlibF/Proof/exact.lean', 'refs':[], 'theorem':True, 'registered':True}]
        graph = self.graph()
        self.assertEqual(len(graph['nodes']), len(self.goals))
        helpers = {row['name']:row for row in graph['auxiliary']}
        self.assertEqual(helpers['Helper.checked']['usedBy'], [self.goals[0]])
        self.assertIn(('exact proofs', self.goals[0]), graph['proofSupport']['edges'])
        self.assertEqual(helpers['Helper.witness']['usedBy'], [])
        self.link_context['files'].append('ZlibF/Proof/exact.lean')
        page = progress.outputs(graph)['docs/progress.md']
        self.assertIn('Helper.checked', page)
        self.assertIn('Helper.witness', page)
        self.assertIn('No fixed-target composition recorded', page)

    def test_dependency_reduction_preserves_each_relationship_kind(self):
        graph = self.graph()
        graph['edges'] += [{'from':self.goals[0],'to':self.goals[2],'kind':'call'},
                           {'from':self.goals[1],'to':self.goals[2],'kind':'call'}]
        visible = progress.visible_dependencies(graph)
        def closure(edges):
            result=set(edges)
            while True:
                more=result | {(a,d) for a,b in result for c,d in result if b==c}
                if more==result:return result
                result=more
        for kind in ['call','proof']:
            original={(e['from'],e['to']) for e in graph['edges'] if e['kind']==kind}
            reduced={(a,b) for a,b,k in visible if k==kind}
            self.assertEqual(closure(original),closure(reduced))
            self.assertTrue(reduced<=original)

    def test_complete_map_fails_before_emitting_an_oversized_renderer_input(self):
        graph = self.graph()
        graph['nodes'][0]['label'] = 'x' * 51000
        with self.assertRaisesRegex(ValueError, 'renderer text budget'):
            progress.mermaid(graph)

class ExportIntegrationTests(unittest.TestCase):
    def test_actual_compiled_theorem_bodies_supply_dependency_references(self):
        lake = shutil.which('lake') or str(Path.home() / '.elan/bin/lake')
        lean = subprocess.check_output([lake, 'env', 'which', 'lean'], cwd=REPO, text=True).strip()
        leanpath = subprocess.check_output([lake, 'env', 'printenv', 'LEAN_PATH'], cwd=REPO, text=True).strip()
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root/'ZlibF.lean').write_text('namespace ZlibF\ndef Goal.sample : Prop := True\n'
                'theorem helper : Goal.sample := True.intro\n'
                'theorem result : Goal.sample := helper\nend ZlibF\n')
            (root/'goals.txt').write_text('ZlibF.Goal.sample\n')
            (root/'theorems.txt').write_text('ZlibF.result\n')
            env = dict(os.environ, LEAN_PATH=directory + os.pathsep + leanpath,
                       PATH=str(Path(lean).parent) + os.pathsep + os.environ.get("PATH", ""))
            subprocess.run([lean, '-o', 'ZlibF.olean', 'ZlibF.lean'], cwd=root, env=env,
                           check=True, capture_output=True, text=True, timeout=60)
            output = subprocess.check_output([lean, '--run', str(REPO/'scripts/proof-progress.lean'),
                'goals.txt', 'theorems.txt'], cwd=root, env=env, text=True, timeout=60)
            declarations = {row['name']:row for row in json.loads(output)['declarations']}
            self.assertIn('ZlibF.helper', declarations['ZlibF.result']['refs'])
            self.assertTrue(declarations['ZlibF.result']['registered'])

if __name__ == '__main__':
    unittest.main()
