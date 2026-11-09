"""Regression checks for preserving the recorded progress inventory in HTML."""
from pathlib import Path
import re
import sys
import unittest
from html.parser import HTMLParser

SITE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SITE))
from progress import parse_progress, render_progress

SOURCE = (SITE.parents[1] / 'docs/progress.md').read_text()


class InventoryTests(unittest.TestCase):
    def test_every_drawn_target_and_observed_connection_is_retained(self):
        data = parse_progress(SOURCE)
        drawn_nodes = set(re.findall(r'^    (n\d+)\[', SOURCE, re.M))
        self.assertEqual(drawn_nodes, {target.node for target in data.targets})
        self.assertEqual(len(data.targets), len({target.anchor for target in data.targets}))
        self.assertLess(len(data.drawn_edges), len(data.edges))
        self.assertTrue(set(data.drawn_edges) <= set(data.edges))
        # Similar C names had the same original Markdown anchor. Keep both rows.
        getters = {target.name: target for target in data.targets if target.name in {'gzgetc', 'gzgetc_'}}
        self.assertEqual(set(getters), {'gzgetc', 'gzgetc_'})
        self.assertNotEqual(getters['gzgetc'].anchor, getters['gzgetc_'].anchor)

    def test_both_languages_retain_targets_and_resolvable_dependency_links(self):
        data = parse_progress(SOURCE)
        class Links(HTMLParser):
            def __init__(self):
                super().__init__(); self.ids = []; self.links = []
            def handle_starttag(self, tag, attrs):
                attrs = dict(attrs)
                if 'id' in attrs: self.ids.append(attrs['id'])
                if 'href' in attrs: self.links.append(attrs['href'])
        for lang in ('en', 'zh'):
            page = Links(); page.feed(render_progress(SOURCE, lang))
            self.assertEqual(len(page.ids), len(set(page.ids)))
            self.assertTrue({'pg-'+target.node for target in data.targets} <= set(page.ids))
            for link in page.links:
                if link.startswith('#pg-'): self.assertIn(link[1:], page.ids)
            for target in data.targets: self.assertIn('#'+target.anchor, page.links)

    def test_missing_node_is_rejected(self):
        broken = re.sub(r'^    n19\[.*\n', '', SOURCE, count=1, flags=re.M)
        with self.assertRaises(ValueError): parse_progress(broken)

    def test_missing_evidence_row_is_rejected(self):
        broken = re.sub(r'^\| <a id="target-zlibf-spec-public-goal-compressbound".*\n', '', SOURCE, count=1, flags=re.M)
        with self.assertRaises(ValueError): parse_progress(broken)

    def test_blocker_mismatch_is_rejected(self):
        with self.assertRaises(ValueError): parse_progress(SOURCE.replace('  class n73 obstacle\n', ''))

    def test_unsupported_drawn_dependency_is_rejected(self):
        broken = SOURCE.replace('  n128 --> n129', '  n128 --> n129\n  n19 --> n20', 1)
        with self.assertRaises(ValueError): parse_progress(broken)

    def test_unknown_observed_target_is_rejected(self):
        broken = SOURCE.replace('| [pointer_advance_preserves_low_bits](#target-c-byteaddress-spec-goal-pointer-advance-preserves-low-bits) |', '| [missing](#target-missing) |', 1)
        with self.assertRaises(ValueError): parse_progress(broken)

    def test_stale_count_is_rejected(self):
        broken = re.sub(r'Exact proofs: \d+ registered', 'Exact proofs: 0 registered', SOURCE, count=1)
        with self.assertRaises(ValueError): parse_progress(broken)


if __name__ == '__main__': unittest.main()
