"""A dependency diagram must show edges and retain every selectable target."""
from collections import Counter
from html.parser import HTMLParser
import json
from pathlib import Path
import re
import sys
import unittest

sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
from progress import parse_progress, GROUPS, STATUS
from progress_graph import render_graph, POSITIONS, NODE_W, NODE_H

SOURCE=(Path(__file__).resolve().parents[3]/'docs/progress.md').read_text()


class DiagramHTML(HTMLParser):
    def __init__(self,source):
        super().__init__();self.payload='';self.in_data=False;self.nodes=[];self.edges=[];self.options=[];self.paths=0;self.feed(source)
    def handle_starttag(self,tag,attrs):
        a=dict(attrs)
        if tag=='script' and 'data-progress-graph-data' in a:self.in_data=True
        if 'data-graph-group' in a:self.nodes.append(a)
        if 'data-edge-count' in a:self.edges.append(a)
        if tag=='option':self.options.append(a['value'])
        if tag=='path' and 'marker-end' in a:self.paths+=1
    def handle_endtag(self,tag):
        if tag=='script':self.in_data=False
    def handle_data(self,data):
        if self.in_data:self.payload+=data


class DependencyDiagram(unittest.TestCase):
    def test_all_targets_and_directed_connections_are_available_in_both_languages(self):
        data=parse_progress(SOURCE);by_anchor={t.anchor:t.node for t in data.targets}
        expected={(by_anchor[a],by_anchor[b],kind) for a,b,kind in data.edges}
        for lang in ('zh','en'):
            page=DiagramHTML(render_graph(data,lang,GROUPS,STATUS));payload=json.loads(page.payload)
            self.assertEqual(set(page.options),{t.node for t in data.targets})
            self.assertEqual({t['id'] for t in payload['targets']},set(page.options))
            self.assertEqual({(e['from'],e['to'],e['kind']) for e in payload['edges']},expected)
            self.assertEqual(len(page.options),len(set(page.options)))

    def test_component_edges_and_internal_counts_account_for_every_connection(self):
        data=parse_progress(SOURCE);by_anchor={t.anchor:t.group for t in data.targets}
        expected=Counter((by_anchor[a],by_anchor[b],kind) for a,b,kind in data.edges if by_anchor[a]!=by_anchor[b])
        page=DiagramHTML(render_graph(data,'zh',GROUPS,STATUS))
        actual={(e['data-from'],e['data-to'],e['data-kind']):int(e['data-edge-count']) for e in page.edges}
        self.assertEqual(actual,dict(expected))
        self.assertEqual(page.paths,len(expected))
        self.assertGreater(page.paths,0,'The overview must contain arrows, not only cards')
        self.assertEqual(sum(actual.values())+sum(int(n['data-internal-count']) for n in page.nodes),len(data.edges))

    def test_manually_placed_components_do_not_overlap(self):
        data=parse_progress(SOURCE)
        self.assertEqual(set(data.groups),set(POSITIONS))
        for a,(ax,ay) in POSITIONS.items():
            for b,(bx,by) in POSITIONS.items():
                if a>=b:continue
                overlap=ax<bx+NODE_W and bx<ax+NODE_W and ay<by+NODE_H and by<ay+NODE_H
                self.assertFalse(overlap,(a,b,'overlapping dependency nodes'))


if __name__=='__main__':unittest.main()
