#!/usr/bin/env python3
"""Build a read-only goal graph from the compiled environment and the real registries.

Run from any directory. Outputs are generated views, never verification evidence.
No registry, specification, proof, audit lock or acceptance policy is changed.
"""
from __future__ import annotations
import argparse
from collections import Counter, defaultdict
import hashlib
import html
import json
from pathlib import Path
import posixpath
import re
import shutil
import subprocess
import sys
import tempfile
import time
from urllib.parse import quote

ROOT = Path(__file__).resolve().parents[1]
GROUPS = {'queries': 'Library queries', 'checksums': 'Checksums', 'addresses': 'Byte-address model', 'inflate': 'Inflate streams',
          'fast': 'Fast decoder obligations', 'tables': 'Decode-table obligations',
          'copy': 'Match-copy mathematics', 'deflate': 'Deflate streams', 'back': 'Callback decoding', 'gzip': 'Gzip files',
          'buffers': 'Whole-buffer operations', 'models': 'Format and API models',
          'lifecycle': 'Lifecycles and call sequences', 'internal': 'Internal proof obligations'}
STATUSES = {'registered': 'Registered proof', 'local': 'Locally checked',
            'open': 'Not proved', 'blocked': 'Blocked'}

# The Chinese twin docs/progress.zh.md carries the same generated region. It is written from the same
# graph, with these fixed phrases, so a regeneration updates both pages (the documentation site needs
# every target anchor on both).
GROUPS_ZH = {'queries': '库信息查询', 'checksums': '校验和', 'addresses': '字节地址模型', 'inflate': '解压流',
             'fast': '快速解码器的证明义务', 'tables': '解码表的证明义务', 'copy': '回引用复制',
             'deflate': '压缩流', 'back': '回调解码', 'gzip': 'gzip 文件', 'buffers': '完整缓冲区操作',
             'models': '格式与 API 模型', 'lifecycle': '生命周期与调用序列', 'internal': '内部证明义务'}
STATUSES_ZH = {'registered': '已登记证明', 'local': '本地已检查', 'open': '未证明', 'blocked': '存在阻碍'}
COVERAGE_ZH = {'unproved': '未证明', 'default': '默认输入', 'common': '常见输入', 'all': '陈述所允许的全部输入'}
FAMILIES_ZH = {'runtime object and arithmetic lemmas': '运行时对象与算术引理', 'heap-free mathematics': '不涉及堆的数学证明',
               'format-model lemmas': '格式模型引理', 'API-model lemmas': 'API 模型引理', 'specification lemmas': '规格引理',
               'api-model proofs': 'API 模型证明', 'format proofs': '格式证明',
               'deflate construction proofs': 'deflate 状态构造证明', 'deflate entry composition': 'deflate 入口组合证明',
               'inflate entry composition': 'inflate 入口组合证明', 'public entry composition': '公开入口组合证明',
               'inflate mode and exit proofs': 'inflate 模式与退出证明', 'inflate storage and bit proofs': 'inflate 存储与读位证明',
               'deflate window and match proofs': 'deflate 窗口与匹配证明', 'deflate lifecycle proofs': 'deflate 生命周期证明',
               'tree construction and emission proofs': '编码树构造与输出证明', 'ByteAddress proofs': 'ByteAddress 字节地址模型证明'}


def family_zh(label):
    if label in FAMILIES_ZH: return FAMILIES_ZH[label]
    return re.sub(r'^(.*) proofs$', r'\1 的证明', label)


def read_readiness_zh():
    """Chinese readiness labels by anchor, from the twin's own readiness table (absent: English kept)."""
    path = ROOT / 'docs/progress.zh.md'
    if not path.is_file(): return {}
    text = path.read_text()
    start, end = '<!-- proof-readiness:start -->', '<!-- proof-readiness:end -->'
    if text.count(start) != 1 or text.count(end) != 1: return {}
    labels = {}
    for line in text.split(start, 1)[1].split(end, 1)[0].splitlines():
        if not line.startswith('| `'): continue
        cells = [cell.strip() for cell in line.strip('|').split('|')]
        anchors = re.findall(r'<a id="(readiness-[a-z0-9-]+)"></a>', cells[-1])
        if len(cells) == 3 and anchors: labels[anchors[0]] = cells[1]
    return labels

def github_repository(remote):
    name = re.sub(r'^(?:git@github\.com:|ssh://git@github\.com/|https://github\.com/)', '', remote.strip())
    name = name.removesuffix('/').removesuffix('.git')
    if not re.fullmatch(r'[\w.-]+/[\w.-]+', name):
        raise ValueError('origin must name a GitHub repository for diagram links')
    return 'https://github.com/' + name

def recorded_link_revision():
    """The revision the current page links to. It is kept while the page shows the same facts, so a
    proof edit that changes nothing shown does not make the page stale."""
    path = ROOT / 'docs/progress.md'
    if not path.is_file(): return None
    revision = re.search(r'<!-- proof-link-revision: ([0-9a-f]{40}) -->', path.read_text())
    return revision[1] if revision else None

def link_context(revision=None):
    def git(*args): return subprocess.check_output(['git', *args], cwd=ROOT, text=True).strip()
    revision = revision or recorded_link_revision() or git('rev-parse', 'HEAD')
    repository = github_repository(git('remote', 'get-url', 'origin'))
    files = git('ls-tree', '-r', '--name-only', revision).splitlines()
    def page(path): return git('show', revision + ':' + path) if path in files else ''
    progress = page('docs/progress.md')

    return {'repository': repository, 'revision': revision, 'files': files,
            'progressAnchors': re.findall(r'<a id="([^"]+)"', progress),
            'progressHeadings': [re.sub(r'[^\w\- ]', '', title.lower()).replace(' ', '-')
                                for title in re.findall(r'^#{1,6} (.+)$', progress, re.M)]}

def snapshot_url(graph, path, fragment='', tree=False):
    context = graph['links']
    if tree:
        exists = any(name.startswith(path + '/') for name in context['files'])
    else: exists = path in context['files']
    if not exists: raise ValueError(f'commit {path} before generating diagram snapshot links')
    url = f'{context["repository"]}/{"tree" if tree else "blob"}/{context["revision"]}/{quote(path, safe="/")}'
    return url + ('#' + quote(fragment, safe='-_') if fragment else '')

def target_url(graph, node):
    if node['blocker']:
        anchor = node['blocker']['anchor']
        if anchor not in graph['links']['progressHeadings']:
            raise ValueError('commit blocker reasons before generating diagram snapshot links')
        return snapshot_url(graph, 'docs/progress.md', anchor)
    return snapshot_url(graph, node['source'], f'L{node["line"]}' if node['line'] else '')

def group_url(graph, key):
    paths = [n['source'] for n in graph['nodes'] if n['group'] == key]
    common = posixpath.commonpath(paths)
    return snapshot_url(graph, common, tree=common not in graph['links']['files'])

def read_blockers():
    """Progress remains the only maintained list of remaining work and blockers."""
    blockers = {}
    heading = None
    for line in (ROOT / 'docs/progress.md').read_text().splitlines():
        match = re.fullmatch(r'#{2,6} (.+)', line)
        if match:
            title = match[1]
            heading = {'title': title, 'anchor': re.sub(r'[^\w\- ]', '', title.lower()).replace(' ', '-')}
        if not line.startswith('<!-- proof-blocker:'): continue
        match = re.fullmatch(r'<!-- proof-blocker: ([\w.]+) -->', line)
        if not match or not heading: raise ValueError('invalid proof blocker marker in progress')
        name = match[1]
        if name in blockers: raise ValueError(f'duplicate proof blocker: {name}')
        blockers[name] = dict(heading)
    return blockers

def read_readiness():
    """Reviewed proof work is maintained once, in progress; it never grants proof status."""
    text = (ROOT / 'docs/progress.md').read_text()
    start, end = '<!-- proof-readiness:start -->', '<!-- proof-readiness:end -->'
    if start not in text and end not in text: return {}
    if text.count(start) != 1 or text.count(end) != 1:
        raise ValueError('invalid proof readiness markers in progress')
    if text.index(start) >= text.index(end): raise ValueError('reversed proof readiness markers')
    rows = text.split(start, 1)[1].split(end, 1)[0].splitlines()
    result = {}
    anchors = set()
    for line in rows:
        if not line.startswith('| `'): continue
        cells = [cell.strip() for cell in line.strip('|').split('|')]
        if len(cells) != 3 or not cells[1] or not cells[2]:
            raise ValueError('invalid proof readiness row')
        targets = re.findall(r'`([A-Za-z0-9_]+)`', cells[0])
        if not targets or not re.fullmatch(r'(?:`[A-Za-z0-9_]+`)(?:, `[A-Za-z0-9_]+`)*', cells[0]):
            raise ValueError('invalid proof readiness target names')
        if not re.fullmatch(r'(?:Start|Needs|Blocked): [A-Za-z0-9 ,/-]+', cells[1]):
            raise ValueError('invalid proof readiness label')
        row_anchors = re.findall(r'<a id="(readiness-[a-z0-9-]+)"></a>', cells[2])
        if len(row_anchors) > 1 or (row_anchors and row_anchors[0] in anchors):
            raise ValueError('duplicate proof readiness anchor')
        anchor = row_anchors[0] if row_anchors else 'public-api-proof-readiness'
        if row_anchors: anchors.add(anchor)
        for target in targets:
            name = 'ZlibF.Spec.Public.Goal.' + target
            if name in result: raise ValueError('duplicate proof readiness target: ' + name)
            result[name] = {'label': cells[1], 'anchor': anchor}
    if not result: raise ValueError('empty proof readiness table')
    if '### Public API proof readiness' not in text:
        raise ValueError('missing public proof readiness heading')
    return result


def names(path):
    result = [s.strip() for s in path.read_text().splitlines() if s.strip() and not s.lstrip().startswith('#')]
    if not result or len(result) != len(set(result)): raise ValueError(f'empty or duplicate registry: {path.name}')
    return result

def input_files():
    return sorted([ROOT / 'ZlibF.lean', *ROOT.joinpath('ZlibF').rglob('*.lean'),
                   ROOT / 'tests/audit/goals.txt', ROOT / 'tests/audit/theorems.txt',
                   ROOT / 'tests/audit/public-api.json'])

def fingerprint():
    digest = hashlib.sha256()
    for path in input_files():
        digest.update(str(path.relative_to(ROOT)).encode() + b'\0' + path.read_bytes() + b'\0')
    digest.update(json.dumps(read_blockers(), sort_keys=True).encode())
    digest.update(json.dumps(read_readiness(), sort_keys=True).encode())
    return digest.hexdigest()

def group(name):
    short = name.rsplit('.', 1)[-1]
    if name.startswith('C.ByteAddress.Spec.Goal.'): return 'addresses'
    if name.startswith('ZlibF.Spec.Api.'): return 'models'
    if name.startswith('Zlib.Inffast.'): return 'fast'
    if name.startswith('Zlib.Inftrees.'): return 'tables'
    if name.startswith(('ZlibF.Math.LZ77Copy.', 'ZlibF.Math.LZ77History.')): return 'copy'
    if not name.startswith('ZlibF.Spec.Public.Goal.'): return 'internal'
    if short.endswith('_sequence') or short.endswith('_initialisation_domain'): return 'lifecycle'
    if short in {'zlibVersion', 'zlibCompileFlags', 'zError', 'compressBound', 'compressBound_z', 'get_crc_table'}: return 'queries'
    if short.startswith(('adler', 'crc')): return 'checksums'
    if short.startswith('inflateBack'): return 'back'
    if short.startswith('inflate'): return 'inflate'
    if short.startswith('deflate'): return 'deflate'
    if short.startswith('gz'): return 'gzip'
    return 'buffers'

def line_of(path, declaration):
    if not path or not (ROOT / path).is_file(): return None
    leaf = declaration.rsplit('.', 1)[-1]
    pattern = re.compile(r'\b(?:theorem|def)\s+(?:Goal\.)?' + re.escape(leaf) + r'\b')
    for number, text in enumerate((ROOT / path).read_text().splitlines(), 1):
        if pattern.search(text): return number
    return None

def build_graph(export, digest, revision=None):
    goals = names(ROOT / 'tests/audit/goals.txt')
    if [row['name'] for row in export['goals']] != goals: raise ValueError('export does not match the complete goal registry')
    blockers = read_blockers()
    unknown = set(blockers) - set(goals)
    if unknown: raise ValueError('blockers refer to unregistered targets: ' + ', '.join(sorted(unknown)))
    readiness = read_readiness()
    if set(readiness) - set(goals):
        raise ValueError('readiness refers to unregistered targets: ' + ', '.join(sorted(set(readiness) - set(goals))))
    manifest = json.loads((ROOT / 'tests/audit/public-api.json').read_text())
    public = {a['goal'] for a in manifest['apis'] if a.get('goal')}
    public.update(manifest.get('sequence_goals', []))
    public.update(manifest.get('nonvacuity_goals', []))
    public.update(manifest.get('safety_goals', []))
    if public - set(goals): raise ValueError('public manifest targets missing from goal registry')
    if {g for g in goals if g.startswith('ZlibF.Spec.Public.Goal.')} - public:
        raise ValueError('public goal missing from public manifest')
    entries = {a['goal']: a for a in manifest['apis'] if a.get('goal') in goals}
    impls = {a['implementation']: g for g, a in entries.items()}
    declarations = {d['name']: d for d in export['declarations']}
    tracked = set(subprocess.check_output(['git', 'ls-files', '-z'], cwd=ROOT, text=True).split('\0'))
    candidates = defaultdict(list)
    # This intentionally finds only candidates. Source text can NEVER grant checked status.
    by_leaf = defaultdict(list)
    for g in goals: by_leaf[g.rsplit('.', 1)[-1]].append(g)
    pattern = re.compile(r'\btheorem\s+([\w.]+)\s*:\s*(?:ZlibF\.Spec\.(?:Public|Api)\.)?Goal\.(\w+)\s*:=')
    for path in sorted(ROOT.joinpath('ZlibF').rglob('*.lean')):
        for match in pattern.finditer(path.read_text()):
            for g in by_leaf.get(match[2], []):
                candidates[g].append({'name': match[1], 'source': str(path.relative_to(ROOT)),
                                      'line': path.read_text()[:match.start()].count('\n') + 1})
    nodes = []
    proof_owner = {}
    for row in export['goals']:
        g = row['name']; proofs = sorted(row['proofs'], key=lambda p: p['name'])
        for p in proofs:
            if not p['allowedAxioms']:
                raise ValueError(f'disallowed axiom dependencies in {p["name"]} for {g}: '
                                 + ', '.join(p['axioms']))
            p['line'] = line_of(p['source'], p['name']); p['committed'] = p['source'] in tracked
            proof_owner[p['name']] = g
        status = 'registered' if any(p['registered'] for p in proofs) else 'local' if proofs else 'open'
        if readiness.get(g, {}).get('label', '').startswith('Blocked:') and g not in blockers:
            raise ValueError('readiness cannot establish a blocker: ' + g)
        if g in blockers:
            if proofs: raise ValueError(f'remove the stale blocker for checked target: {g}')
            status = 'blocked'
        nodes.append({'id': g, 'label': g.rsplit('.', 1)[-1], 'group': group(g), 'status': status,
                      'blocker': blockers.get(g), 'readiness': readiness.get(g), 'scope': 'public' if g in public else 'supporting',
                      'source': row['source'], 'line': line_of(row['source'], g),
                      'description': row['description'], 'proofs': proofs,
                      'candidates': candidates[g] if not proofs else [],
                      'implementation': entries.get(g, {}).get('implementation'),
                      'manual': entries.get(g, {}).get('manual')})
    edges = set()
    helpers = {name: row for name, row in declarations.items()
               if row.get('registered') and row.get('theorem') and name not in proof_owner}
    helper_users = defaultdict(set)
    def add(a, b, kind):
        if a != b and a in goals and b in goals: edges.add((a, b, kind))
    # Real translated calls, including calls through non-public translated helpers.
    for implementation, target in impls.items():
        seen = set(); todo = list(declarations.get(implementation, {}).get('refs', []))
        while todo:
            dep = todo.pop()
            if dep in seen: continue
            seen.add(dep)
            if dep in impls:
                add(impls[dep], target, 'call'); continue
            row = declarations.get(dep)
            if row and row['source'].startswith('ZlibF/Zlib/'): todo.extend(row['refs'])
    for node in nodes:
        g = node['id']
        for dep in declarations.get(g, {}).get('refs', []):
            if dep in goals: add(dep, g, 'definition')
            if not node['implementation'] and dep in impls: add(impls[dep], g, 'definition')
        # Actual references in existing proof terms; unknown future dependencies stay unknown.
        todo = [d for p in node['proofs'] for d in declarations.get(p['name'], {}).get('refs', [])]
        seen = set()
        while todo:
            dep = todo.pop()
            if dep in seen: continue
            seen.add(dep)
            if dep in helpers: helper_users[dep].add(g)
            if dep in proof_owner:
                add(proof_owner[dep], g, 'proof'); continue
            if dep in goals: continue
            row = declarations.get(dep)
            if row: todo.extend(row['refs'])
    return {'version': 1, 'inputSha256': digest, 'links': link_context(revision),
            'counts': dict(Counter(n['status'] for n in nodes)),
            'groups': GROUPS, 'statuses': STATUSES, 'nodes': nodes,
            'edges': [{'from': a, 'to': b, 'kind': k} for a, b, k in sorted(edges)],
            'auxiliary': [{**row, 'line': line_of(row['source'], name), 'usedBy': sorted(helper_users[name])}
                          for name, row in sorted(helpers.items())],
            'proofSupport': proof_support_graph(nodes, declarations,
                {name: row for name, row in declarations.items() if row.get('theorem') and name not in proof_owner}, proof_owner),
            'modules': module_graph(nodes, declarations),
            'acceptance': 'Not a final audit or CI result. Registered and locally checked are distinct from final acceptance.'}

def support_family(path):
    stem = Path(path).stem
    if '/Runtime/' in path: return 'runtime object and arithmetic lemmas'
    if '/Math/' in path: return 'heap-free mathematics'
    if '/Spec/Functional/Format/' in path or '/Spec/Format/' in path: return 'format-model lemmas'
    if '/Spec/Functional/Api/' in path or '/Spec/Api/' in path: return 'API-model lemmas'
    if '/Spec/' in path: return 'specification lemmas'
    if '/Proof/Api/' in path: return 'api-model proofs'
    if '/Proof/Format/' in path: return 'format proofs'
    if stem.startswith('public-deflate-init'): return 'deflate construction proofs'
    if stem.startswith('public-deflate'): return 'deflate entry composition'
    if stem.startswith('public-inflate'): return 'inflate entry composition'
    if stem.startswith('public-'): return 'public entry composition'
    if stem.startswith('inflate.c.main.'): return 'inflate mode and exit proofs'
    if stem.startswith('inflate.c.'): return 'inflate storage and bit proofs'
    if stem.startswith('deflate.c.engine.'): return 'deflate window and match proofs'
    if stem.startswith('deflate.c.init.'): return 'deflate construction proofs'
    if stem.startswith('deflate.c.'): return 'deflate lifecycle proofs'
    if stem.startswith('trees.c.'): return 'tree construction and emission proofs'
    if '.c' in stem: return stem.split('.c', 1)[0] + '.c proofs'
    return stem + ' proofs'

def proof_support_graph(nodes, declarations, helpers, owners):
    # Stop at the nearest theorem instead of drawing its entire
    # transitive closure again at every public goal. Group only actual helpers;
    # a source-file group has no whole-function proof status.
    def nearest(refs):
        todo = list(refs); seen = set(); found = set()
        while todo:
            name = todo.pop()
            if name in seen: continue
            seen.add(name)
            if name in helpers or name in owners:
                found.add(name); continue
            row = declarations.get(name)
            if row: todo.extend(row.get('refs', []))
        return found
    edges = set(); reached = set(); todo = []
    for node in nodes:
        for proof in node['proofs']:
            for dep in nearest(declarations.get(proof['name'], {}).get('refs', [])):
                if dep in helpers:
                    edges.add((support_family(helpers[dep]['source']), node['id'])); todo.append(dep)
    while todo:
        name = todo.pop()
        if name in reached: continue
        reached.add(name)
        caller = support_family(helpers[name]['source'])
        for dep in nearest(declarations.get(name, {}).get('refs', [])):
            if dep in helpers:
                source = support_family(helpers[dep]['source'])
                if source != caller: edges.add((source, caller))
                todo.append(dep)
            elif dep in owners:
                edges.add((owners[dep], caller))
    groups = defaultdict(list)
    for name in sorted(reached): groups[support_family(helpers[name]['source'])].append(helpers[name])
    return {'nodes': [{'id': name, 'members': members} for name, members in sorted(groups.items())],
            'edges': sorted(edges)}

def select_view(graph, scope):
    nodes = [n for n in graph['nodes'] if n['scope'] == scope]
    ids = {n['id'] for n in nodes}
    return {**graph, 'nodes': nodes, 'counts': dict(Counter(n['status'] for n in nodes)),
            'edges': [e for e in graph['edges'] if e['from'] in ids and e['to'] in ids]}

def module_graph(nodes, declarations):
    """Observed module references, with omitted helper modules compressed into paths."""
    selected = {n['source'] for n in nodes if n['scope'] == 'supporting'}
    selected.update(p['source'] for n in nodes if n['scope'] == 'supporting' for p in n['proofs'])
    dependencies = defaultdict(set)
    for row in declarations.values():
        for ref in row.get('refs', []) + row.get('typeRefs', []):
            target = declarations.get(ref)
            if target and target['source'] != row['source']:
                dependencies[row['source']].add(target['source'])
    edges = set()
    for caller in selected:
        todo = list(dependencies[caller]); seen = {caller}
        while todo:
            dependency = todo.pop()
            if dependency in seen: continue
            seen.add(dependency)
            if dependency in selected:
                edges.add((dependency, caller))
            else:
                todo.extend(dependencies[dependency])
    return {'nodes': sorted(selected), 'edges': sorted(edges)}

def target_anchor(node):
    return 'target-' + re.sub(r'[^a-z0-9]+', '-', node['id'].lower()).strip('-')

COVERAGE = {'unproved': ('Not proved', '#e5e7eb', '#374151'),
            'default': ('Default inputs', '#dbeafe', '#1d4ed8'),
            'common': ('Common inputs', '#fef3c7', '#92400e'),
            'all': ('All stated inputs', '#dcfce7', '#166534')}

def input_family(node):
    name = node['id']
    if node['group'] == 'deflate' or name.endswith('.deflate_sequence'): return 'deflate'
    if node['group'] == 'inflate' or name.endswith('.inflate_sequence'): return 'inflate'
    return 'entry'

def coverage_level(node):
    # The current export matches exact, complete fixed goals only. A local
    # branch lemma or a source annotation cannot establish a scoped contract.
    # Default/common colours require reviewed scoped contracts and exact
    # kernel matches before they can be emitted for an incomplete goal.
    return 'all' if node['proofs'] else 'unproved'

def diagram_styles():
    lines = [f'  classDef {key} fill:{fill},color:{text},stroke:{text}'
             for key, (_, fill, text) in COVERAGE.items()]
    lines.append('  classDef obstacle stroke:#b91c1c,stroke-width:3px')
    return lines

def wrapped_label(value):
    parts = re.split(r'(?<=[_.])|(?<=[a-z0-9])(?=[A-Z])', value)
    rows = []; row = ''
    for part in parts:
        if row and len(row) + len(part) > 25:
            rows.append(row); row = ''
        row += part
    if row: rows.append(row)
    return '<br/>'.join(html.escape(row, quote=True) for row in rows)

def visible_dependencies(graph):
    proof = {(e['from'], e['to']) for e in graph['edges'] if e['kind'] == 'proof'}
    calls = {(e['from'], e['to']) for e in graph['edges'] if e['kind'] == 'call'}
    def reduce(edges):
        # Remove an edge only while another path still exists. Sequential
        # removal also preserves reachability in grouped cyclic components.
        kept = set(edges)
        for edge in sorted(edges):
            kept.remove(edge); todo = [edge[0]]; seen = set()
            while todo:
                node = todo.pop()
                if node in seen: continue
                seen.add(node)
                todo.extend(b for a, b in kept if a == node)
            if edge[1] not in seen: kept.add(edge)
        return kept
    return [(a,b,kind) for kind, edges in [('proof',proof),('call',calls)]
            for a,b in sorted(reduce(edges))]

def diagram_url(graph, node):
    # Click links carry the commit as a 12-digit prefix: the full hash on every node would
    # take most of the renderer's 50000-character budget. GitHub resolves the prefix.
    revision = graph['links']['revision']
    return target_url(graph, node).replace('/' + revision + '/', '/' + revision[:12] + '/', 1)

def mermaid(graph):
    indexes = {n['id']: f'n{i}' for i, n in enumerate(graph['nodes'])}
    lines = ['flowchart LR']
    for key, title in GROUPS.items():
        members = [n for n in graph['nodes'] if n['group'] == key]
        if not members: continue
        lines += [f'  subgraph {key}["{title}"]']
        for node in members:
            label = wrapped_label(node['label'])
            if node['scope'] == 'supporting':
                stem = Path(node['source']).stem
                label = wrapped_label(stem) + '<br/>' + label
            if node['status'] == 'local': label += '<br/>Local exact proof'
            if node['blocker']: label += '<br/>Blocked'
            lines.append(f'    {indexes[node["id"]]}["{label}"]:::{coverage_level(node)}')
        lines.append('  end')
        lines.append(f'  style {key} fill:#f9fafb,stroke:#9ca3af,color:#111827')
    for source, target, kind in visible_dependencies(graph):
        if source in indexes and target in indexes:
            arrow = '-->' if kind == 'proof' else '-.->'
            lines.append(f'  {indexes[source]} {arrow} {indexes[target]}')
    for node in graph['nodes']:
        if node['blocker']: lines.append(f'  class {indexes[node["id"]]} obstacle')
        lines.append(f'  click {indexes[node["id"]]} href "{diagram_url(graph, node)}" _blank')
    lines.extend(diagram_styles())
    diagram = '\n'.join(lines)
    if len(diagram) > 50000:
        raise ValueError('complete dependency map exceeds renderer text budget; shorten labels without dropping targets')
    return diagram

START = '<!-- proof-progress:start -->'
END = '<!-- proof-progress:end -->'

def blocker_index(graph, page='progress.md', zh=False):
    groups = defaultdict(list)
    for node in graph['nodes']:
        if node['blocker']: groups[(node['blocker']['anchor'], node['blocker']['title'])].append(node)
    if not groups: return '这一快照中没有记录在案的阻碍。' if zh else 'No documented blockers in this snapshot.'
    lines = ['| 存在阻碍的目标 | 原因与下一步 |' if zh else '| Blocked targets | Reason and next step |', '| --- | --- |']
    for (anchor, title), nodes in sorted(groups.items()):
        targets = ', '.join(f'[{n["label"]}](./{page}#{target_anchor(n)})' for n in nodes)
        lines.append(f'| {targets} | [{title}](./progress.md#{anchor}) |')
    return '\n'.join(lines)

def detail_page(graph):
    rows = []
    for key, title in GROUPS.items():
        members = [n for n in graph['nodes'] if n['group'] == key]
        if not members: continue
        rows += [f'<a id="group-{key}"></a>', '', f'## {title}', '',
                 '| Target statement | Coverage / evidence state | Contract / input range | Proof evidence | Reviewed next work |',
                 '| --- | --- | --- | --- | --- |']
        for node in members:
            source = '../' + node['source'] + (f"#L{node['line']}" if node['line'] else '')
            label = f'<a id="{target_anchor(node)}"></a>[{node["label"]}]({source})'
            evidence = '; '.join(f"[{p['name']}](../{p['source']}" +
                (f"#L{p['line']}" if p.get('line') else '') + ')' for p in node['proofs']) or '—'
            if node['candidates']:
                evidence = 'Unchecked source: ' + '; '.join(f"[{p['name']}](../{p['source']}#L{p['line']})" for p in node['candidates'])
            if node['blocker']:
                evidence += f' [Blocker: {node["blocker"]["title"]}](progress.md#{node["blocker"]["anchor"]})'
            contract = f'[Contract](../{node["manual"]})' if node['manual'] else 'Exact target statement'
            contract += f'; [input range](spec/input-configurations.md#{input_family(node)}-inputs)'
            work = node.get('readiness')
            next_work = f"[{work['label']}](progress.md#{work['anchor']})" if work and node['status'] in {'open', 'blocked'} else ('Prerequisites unreviewed' if node['status'] == 'open' else '—')
            coverage = COVERAGE[coverage_level(node)][0] + ' / ' + STATUSES[node['status']]
            rows.append(f'| {label} | {coverage} | {contract} | {evidence} | {next_work} |')
        rows.append('')
    relations = []
    labels = {n['id']: n['label'] for n in graph['nodes']}
    for kind, title, explanation in [
        ('proof', 'Observed proof dependencies', 'A theorem for the destination actually uses a proof of the source target.'),
        ('call', 'C function calls', 'The destination implementation calls the source entry. This does not require the complete source-entry contract as a proof premise.'),
        ('definition', 'Specification references', 'The destination target definition references the source target or implementation. This is not a proof dependency.')]:
        relations += [f'## {title}', '', explanation, '', '| Source | Destination |', '| --- | --- |']
        for e in graph['edges']:
            if e['kind'] == kind:
                relations.append(f'| [{labels[e["from"]]}](#'+target_anchor({'id':e['from']})+f') | [{labels[e["to"]]}](#'+target_anchor({'id':e['to']})+') |')
        if not any(e['kind'] == kind for e in graph['edges']):
            relations.append('No references of this kind between fixed targets were observed in this snapshot.')
        relations.append('')
    support = graph.get('proofSupport', {'nodes': [], 'edges': []})
    family_labels = {row['id']: row['id'] for row in support['nodes']}
    all_labels = {**labels, **family_labels}
    relations += ['## Proof support relationships', '',
        'These are observed theorem references grouped by source family. Groups carry no whole-file proof status.',
        'Every direct grouped connection is retained here, including arrows reduced in the graph.', '',
        '| Supporting source | Direct destinations |', '| --- | --- |']
    for source in sorted({a for a,b in support['edges']}):
        destinations = ', '.join(all_labels[b] for a,b in support['edges'] if a == source)
        relations.append(f'| {all_labels[source]} | {destinations} |')
    relations.append('')
    auxiliary = ['## Other registered theorems', '',
                 'These declarations are registered supporting execution results, lemmas or witnesses.',
                 'They are not additional fixed targets and do not grant a caller coverage colour.', '',
                 '| Declaration | Used by a fixed-target proof |', '| --- | --- |']
    for proof in graph.get('auxiliary', []):
        source = '../' + proof['source'] + (f"#L{proof['line']}" if proof['line'] else '')
        users = ', '.join(f'[{labels[name]}](#'+target_anchor({'id':name})+')' for name in proof['usedBy']) or 'No fixed-target composition recorded'
        auxiliary.append(f'| [{proof["name"]}]({source}) | {users} |')
    return f"""## Target evidence

<!-- proof-link-revision: {graph['links']['revision']} -->

[Proof narrative](overview.md) · [All-target graph](#proof-progress-graph) · [Input configurations](spec/input-configurations.md)

This index contains **{len(graph['nodes'])} fixed targets**: public execution,
sequence and initialization targets, internal obligations and abstract models.
There is one status graph, in progress. A model result is not implementation refinement.
Input coverage and proof registration are separate. An exact local proof can
cover its complete stated domain while still awaiting registration and CI.
Internal premises remain part of the statement; green does not remove them.
A source-only candidate never grants coverage. Disallowed axioms stop generation.

Why can an isolated node be unfinished? Its proof dependencies have not been
established. Missing arrows neither prove independence nor supply a proof plan.
Some Markdown viewers disable diagram links; use these ordinary source links.

## Status key

<a id="status-registered"></a>Registered proof: an exact checked theorem is listed.
<a id="status-local"></a>Locally checked: an exact theorem exists but is not listed.
<a id="status-open"></a>Not proved: no exact theorem covers this target.
<a id="status-blocked"></a>Blocked: a documented obstacle applies to the target.
These labels do not assign input coverage or replace named-commit CI acceptance.
"All stated inputs" means every input the goal itself states. A goal can state less than zlib.h
allows: [No-fault coverage of zlib.h functions](#no-fault-coverage-of-zlibh-functions) lists the gaps.

{chr(10).join(rows)}
{chr(10).join(relations)}
{chr(10).join(auxiliary)}

## Refresh

Regenerate after proof or registry changes. The generator builds and inspects
exact compiled theorem types. It never changes a proof, target or registry.
It writes this region of this page and of its Chinese twin `docs/progress.zh.md`.
Acceptance remains subject to [checking](checking/README.md).
The view is stale only when what it shows changes: a target, a registration, a proof status, a
link or a line anchor. Its links keep the revision they were generated at until then.
"""

def detail_page_zh(graph):
    """The evidence index of `detail_page` for the Chinese twin: the same rows, anchors and links."""
    readiness_zh = read_readiness_zh()
    rows = []
    for key, title in GROUPS_ZH.items():
        members = [n for n in graph['nodes'] if n['group'] == key]
        if not members: continue
        rows += [f'<a id="group-{key}"></a>', '', f'## {title}', '',
                 '| 目标陈述 | 覆盖范围／证据状态 | 契约／输入范围 | 证明证据 | 已审查的后续工作 |',
                 '| --- | --- | --- | --- | --- |']
        for node in members:
            source = '../' + node['source'] + (f"#L{node['line']}" if node['line'] else '')
            label = f'<a id="{target_anchor(node)}"></a>[{node["label"]}]({source})'
            evidence = '; '.join(f"[{p['name']}](../{p['source']}" +
                (f"#L{p['line']}" if p.get('line') else '') + ')' for p in node['proofs']) or '—'
            if node['candidates']:
                evidence = '未检查的源码：' + '; '.join(f"[{p['name']}](../{p['source']}#L{p['line']})" for p in node['candidates'])
            if node['blocker']:
                evidence += f' [阻碍：{node["blocker"]["title"]}](progress.md#{node["blocker"]["anchor"]})'
            contract = f'[契约](../{node["manual"]})' if node['manual'] else '确切目标陈述'
            contract += f'; [输入范围](spec/input-configurations.md#{input_family(node)}-inputs)'
            work = node.get('readiness')
            if work and node['status'] in {'open', 'blocked'}:
                next_work = f"[{readiness_zh.get(work['anchor'], work['label'])}](progress.md#{work['anchor']})"
            else:
                next_work = '前置义务尚未审查' if node['status'] == 'open' else '—'
            coverage = COVERAGE_ZH[coverage_level(node)] + ' / ' + STATUSES_ZH[node['status']]
            rows.append(f'| {label} | {coverage} | {contract} | {evidence} | {next_work} |')
        rows.append('')
    relations = []
    labels = {n['id']: n['label'] for n in graph['nodes']}
    for kind, title, explanation in [
        ('proof', '已观察到的证明依赖', '左列是被复用的来源目标，右列是使用它的目标。右列目标的定理实际使用了左列目标的证明。'),
        ('call', 'C 函数调用', '右列目标对应的实现调用左列入口。这种调用关系不意味着，证明时必须把左列入口的完整契约作为前提。'),
        ('definition', '规格中的引用', '右列目标的定义引用左列目标或实现。这里记录的是定义中的引用，不是证明依赖。')]:
        relations += [f'## {title}', '', explanation, '', '| 来源 | 目标 |', '| --- | --- |']
        for e in graph['edges']:
            if e['kind'] == kind:
                relations.append(f'| [{labels[e["from"]]}](#'+target_anchor({'id':e['from']})+f') | [{labels[e["to"]]}](#'+target_anchor({'id':e['to']})+') |')
        if not any(e['kind'] == kind for e in graph['edges']):
            relations.append('这一快照中没有观察到固定目标之间的这类引用。')
        relations.append('')
    support = graph.get('proofSupport', {'nodes': [], 'edges': []})
    family_labels = {row['id']: family_zh(row['id']) for row in support['nodes']}
    all_labels = {**labels, **family_labels}
    relations += ['## 辅助证明的引用关系', '',
        '这里把已观察到的定理引用按来源类别分组。一个分组不表示对应文件已经整体证明。',
        '本表保留分组之间的全部直接连接，包括总览图为简化显示而省去的箭头。', '',
        '| 辅助证明来源 | 直接引用它的目标 |', '| --- | --- |']
    for source in sorted({a for a,b in support['edges']}):
        destinations = ', '.join(all_labels[b] for a,b in support['edges'] if a == source)
        relations.append(f'| {all_labels[source]} | {destinations} |')
    relations.append('')
    auxiliary = ['## 其他已登记定理', '',
                 '这些声明是已经登记的辅助执行结果、引理或见证。',
                 '它们不是额外的固定目标，也不能单凭这些声明就为调用者标记某种输入覆盖状态。', '',
                 '| 声明 | 被固定目标的证明使用 |', '| --- | --- |']
    for proof in graph.get('auxiliary', []):
        source = '../' + proof['source'] + (f"#L{proof['line']}" if proof['line'] else '')
        users = ', '.join(f'[{labels[name]}](#'+target_anchor({'id':name})+')' for name in proof['usedBy']) or '未记录到固定目标的组合关系'
        auxiliary.append(f'| [{proof["name"]}]({source}) | {users} |')
    return f"""## 目标证据

<!-- proof-link-revision: {graph['links']['revision']} -->

[证明讲解](overview.md) · [全部目标图](#proof-progress-graph) · [输入配置](spec/input-configurations.md)

本索引包含 **{len(graph['nodes'])} 个固定目标**，分为公开接口执行、调用序列、初始化、实现层义务和抽象模型。每个目标分别列出输入范围、登记情况、证明正文和剩余工作。
抽象模型研究输入输出的数学关系；实现目标还要证明真实执行符合这些关系。一个本地证明完成后，仍需登记，并在具体提交上通过 CI 验收。所有证明都保留命题中写明的前置条件。
依赖区展示记录中已经建立的联系。未完成目标还需要哪些证明，见本页后面的具体工作清单。出现不允许的公理时，生成过程会停止。

## 状态说明

<a id="status-registered"></a>已登记证明：存在精确覆盖该目标、经过检查且列入登记表的定理。
<a id="status-local"></a>本地已检查：存在精确覆盖该目标的定理，但尚未列入登记表。
<a id="status-open"></a>未证明：还没有精确覆盖该目标的定理。
<a id="status-blocked"></a>存在阻碍：已有文档记录影响该目标的具体障碍。
输入覆盖范围单独列出；CI 验收对应具体提交。
“陈述所允许的全部输入”指目标自身陈述的每个输入。目标陈述的输入可能少于 zlib.h 允许的范围：
[zlib.h 函数的无故障覆盖](#no-fault-coverage-of-zlibh-functions)列出了这些差距。

{chr(10).join(rows)}
{chr(10).join(relations)}
{chr(10).join(auxiliary)}

## 更新记录

证明或登记表发生变化后，需要重新生成本页。生成过程会编译并检查
定理的精确类型，不会修改证明、目标或登记表。生成器同时写出英文页和本页。
结果是否通过项目验收，仍须依据[检查规则](checking/README.md)。
只有当本页展示的内容发生变化时（目标、登记、证明状态、链接或行锚点），本页才算过期。在此之前，
链接保持生成时的修订版本。
"""


def zh_block(graph):
    counts = graph['counts']
    public_count = sum(n['scope'] == 'public' for n in graph['nodes'])
    return f"""{START}
## 证明进度图

**共有 {len(graph['nodes'])} 个固定目标：{public_count} 个公开目标，{len(graph['nodes'])-public_count} 个支撑目标。**
精确覆盖相应目标的证明中，{counts.get('registered',0)} 个已登记，{counts.get('local',0)} 个仅在本地检查。
这些数字按目标计数，不表示验证工作量的完成百分比，也不代表最终 CI 结果。

**输入覆盖范围的颜色：** ⬜ 未证明 · 🟦 默认输入 · 🟨 常见输入 · 🟩 目标陈述所允许的全部输入。
各档范围统一定义在[输入配置](spec/input-configurations.md)中。
完整的固定目标证明，必须覆盖该目标的确切陈述所允许的全部输入。
若只证明默认输入或常见输入，也必须有经过检查、明确限定范围的契约；局部分支引理和手工填写的标签不能代替这种证明。
输入覆盖范围、证明是否登记、CI 是否通过，是三件不同的事。
红色边框表示已记录的阻碍，不会抹去该目标已经建立的其他覆盖结果。

每个当前固定目标只出现一次。公开 API、内部证明义务和抽象模型分组呈现。
实线表示固定目标之间实际存在的证明复用关系，追踪范围包含经辅助引理间接发生的引用。
虚线表示 C 函数调用，方向由被调用者指向调用者。它并不表示可以把被调用者的完整 API 契约当作证明前提：例如，默认初始化 `Init` 可以独立于通用初始化 `Init2` 完成证明。
只有在同类路径仍然存在时，图中才会省略冗余箭头。[证据索引](progress.md)保留了每条观察到的连接、规格引用和支撑证明族。
这些辅助证明不是额外的最终目标。缺少箭头既不能说明两个目标彼此独立，也不能列全今后需要完成的证明义务。

```mermaid
{mermaid(graph)}
```

展开组件后，再展开一个目标，即可查看它的输入范围、状态和双向依赖。[证据索引](progress.md)保留提交 `{graph['links']['revision'][:7]}` 的目标与证明链接。

{blocker_index(graph, zh=True)}

""" + detail_page_zh(graph) + END


def outputs(graph):
    counts = graph['counts']
    public_count = sum(n['scope'] == 'public' for n in graph['nodes'])
    block = f"""{START}
## Proof progress graph

**{len(graph['nodes'])} fixed targets: {public_count} public and {len(graph['nodes'])-public_count} supporting.**
Exact proofs: {counts.get('registered',0)} registered and {counts.get('local',0)} local only.
These counts are not a percentage of verification effort or a final CI result.

**Input coverage colours:** ⬜ not proved · 🟦 default inputs · 🟨 common inputs · 🟩 all stated inputs.
The input ranges are defined once in [input configurations](spec/input-configurations.md).
A complete fixed-goal proof covers all inputs admitted by that exact statement.
Default/common coverage requires an exact checked scoped contract; branch lemmas
and manually assigned labels cannot grant it. Registration and CI remain separate.
A red border marks a recorded blocker without erasing other established coverage.

Every current fixed target appears once. Public APIs, internal obligations and
abstract models stay in separate groups. Solid arrows show actual proof reuse
between fixed targets, following references through auxiliary lemmas. Dotted
arrows show C calls from callee to caller. They do not make the callee's complete
API contract a proof premise: default Init can be proved independently of
universal Init2. Redundant arrows are omitted only when a path of the same kind
remains. The [evidence index](progress.md) retains every observed connection,
specification references and supporting proof families. These helpers are not
extra final targets. Missing arrows do not establish independence or enumerate
future proof obligations.

```mermaid
{mermaid(graph)}
```

Each node opens its exact target or blocker at the fixed source snapshot
`{graph['links']['revision'][:7]}`. Some viewers disable diagram links; the
[evidence index](progress.md) provides ordinary links and all proof references.

{blocker_index(graph)}
{END}"""
    generated = block.removesuffix(END) + "\n\n" + detail_page(graph) + END
    page = (ROOT / 'docs/progress.md').read_text()
    if START in page or END in page:
        if page.count(START) != 1 or page.count(END) != 1:
            raise ValueError('invalid progress markers')
        before, rest = page.split(START, 1)
        _, after = rest.split(END, 1)
        page = before + generated + after
    else:
        marker = '## Recorded checkpoint'
        if marker not in page: raise ValueError('progress insertion point missing')
        page = page.replace(marker, generated + '\n\n' + marker, 1)
    result = {'docs/progress.md': page}
    twin_path = ROOT / 'docs/progress.zh.md'
    if twin_path.is_file():
        twin = twin_path.read_text()
        if twin.count(START) != 1 or twin.count(END) != 1:
            raise ValueError('invalid progress markers in the Chinese twin')
        before, rest = twin.split(START, 1)
        _, after = rest.split(END, 1)
        twin = before + zh_block(graph) + after
        # The stamp says the twin translates the English page. Only the generated region changed in
        # both, so a twin that was current stays current; a stale twin keeps its stale stamp.
        stamp = re.search(r'source-sha256:\s*([0-9a-f]{64})', twin)
        old = (ROOT / 'docs/progress.md').read_text()
        if stamp and stamp[1] == hashlib.sha256(old.encode()).hexdigest():
            twin = twin.replace(stamp[1], hashlib.sha256(page.encode()).hexdigest(), 1)
        result['docs/progress.zh.md'] = twin
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true', help='reject missing or stale generated views')
    args = parser.parse_args()
    lake = shutil.which('lake') or str(Path.home() / '.elan/bin/lake')
    digest = fingerprint()
    with tempfile.TemporaryDirectory(prefix='proof-progress-') as work:
        log = Path(work) / 'build.log'
        with log.open('w') as output: result = subprocess.run([lake, '--rehash', '--no-cache', 'build', 'ZlibF'], cwd=ROOT, stdout=output, stderr=subprocess.STDOUT)
        if result.returncode: raise RuntimeError('root build failed:\n' + log.read_text()[-5000:])
        result = subprocess.run([lake, 'env', 'lean', '--run', 'scripts/proof-progress.lean'], cwd=ROOT, capture_output=True, text=True, check=True)
        export = json.loads(result.stdout)
    if fingerprint() != digest: raise RuntimeError('proof inputs changed during generation; rerun for a consistent snapshot')
    # The page is generated first with the links of the recorded revision. If that equals the page,
    # nothing it shows has changed, whatever the proof inputs did.
    # A new target can need a file or anchor the recorded revision lacks; then the page is stale too.
    try:
        graph = build_graph(export, digest)
        generated = outputs(graph)
        fresh = all((ROOT / p).is_file() and (ROOT / p).read_text() == content for p, content in generated.items())
    except ValueError as error:
        if args.check: raise
        fresh = False
    if not args.check and not fresh:
        head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip()
        graph = build_graph(export, digest, head)
        generated = outputs(graph)
    if args.check:
        stale = [p for p, content in generated.items() if not (ROOT / p).is_file() or (ROOT / p).read_text() != content]
        if stale: raise RuntimeError('stale progress views: ' + ', '.join(stale))
    else:
        # Only the short shared-document write holds the publication lock.
        lock_path = subprocess.check_output(['git', 'rev-parse', '--git-path', 'dev-publish.lock'],
                                            cwd=ROOT, text=True).strip()
        lock = (ROOT / lock_path).resolve()
        deadline = time.monotonic() + 30
        while True:
            try:
                lock.mkdir()
                break
            except FileExistsError:
                if time.monotonic() >= deadline: raise RuntimeError('another worker holds the publication lock')
                time.sleep(.25)
        owner = lock / 'proof-progress-owner.txt'
        owner.write_text('proof-progress document generation\n')
        try:
            if fingerprint() != digest: raise RuntimeError('proof inputs changed while waiting for the write lock; rerun')
            # Re-read progress under the lock, preserving maintained status and next-work prose.
            generated = outputs(graph)
            for path, content in generated.items(): (ROOT / path).write_text(content)
        finally:
            owner.unlink()
            lock.rmdir()
    print(json.dumps({'targets': len(graph['nodes']), 'statuses': graph['counts'], 'edges': len(graph['edges']), 'checked': args.check}, ensure_ascii=False))

if __name__ == '__main__':
    try: main()
    except (ValueError, RuntimeError, subprocess.CalledProcessError) as error:
        print(f'Progress generation failed: {error}', file=sys.stderr); sys.exit(1)
