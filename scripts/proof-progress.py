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
          'deflate': 'Deflate streams', 'back': 'Callback decoding', 'gzip': 'Gzip files',
          'buffers': 'Whole-buffer operations', 'models': 'Format and API models',
          'lifecycle': 'Lifecycles and call sequences', 'internal': 'Internal proof obligations'}
STATUSES = {'registered': 'Registered proof', 'local': 'Locally checked',
            'open': 'Not proved', 'blocked': 'Blocked'}

def github_repository(remote):
    name = re.sub(r'^(?:git@github\.com:|ssh://git@github\.com/|https://github\.com/)', '', remote.strip())
    name = name.removesuffix('/').removesuffix('.git')
    if not re.fullmatch(r'[\w.-]+/[\w.-]+', name):
        raise ValueError('origin must name a GitHub repository for diagram links')
    return 'https://github.com/' + name

def recorded_link_revision(digest):
    path = ROOT / 'docs/progress.md'
    if not path.is_file(): return None
    text = path.read_text()
    revision = re.search(r'<!-- proof-link-revision: ([0-9a-f]{40}) -->', text)
    fingerprint = re.search(r'Input fingerprint: `([0-9a-f]+)`', text)
    if revision and fingerprint and fingerprint[1] == digest: return revision[1]
    return None

def link_context(digest):
    def git(*args): return subprocess.check_output(['git', *args], cwd=ROOT, text=True).strip()
    revision = recorded_link_revision(digest) or git('rev-parse', 'HEAD')
    repository = github_repository(git('remote', 'get-url', 'origin'))
    files = git('ls-tree', '-r', '--name-only', revision).splitlines()
    def page(path): return git('show', revision + ':' + path) if path in files else ''
    progress = page('docs/progress.md')
    overview = page('docs/overview.md')
    return {'repository': repository, 'revision': revision, 'files': files,
            'progressAnchors': re.findall(r'<a id="([^"]+)"', progress),
            'overviewAnchors': [re.sub(r'[^\w\- ]', '', title.lower()).replace(' ', '-')
                                for title in re.findall(r'^#{1,6} (.+)$', overview, re.M)]}

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
        if anchor not in graph['links']['overviewAnchors']:
            raise ValueError('commit blocker reasons before generating diagram snapshot links')
        return snapshot_url(graph, 'docs/overview.md', anchor)
    return snapshot_url(graph, node['source'], f'L{node["line"]}' if node['line'] else '')

def group_url(graph, key):
    paths = [n['source'] for n in graph['nodes'] if n['group'] == key]
    common = posixpath.commonpath(paths)
    return snapshot_url(graph, common, tree=common not in graph['links']['files'])

def read_blockers():
    """Overview remains the only maintained list of remaining work and blockers."""
    blockers = {}
    heading = None
    for line in (ROOT / 'docs/overview.md').read_text().splitlines():
        match = re.fullmatch(r'#{2,6} (.+)', line)
        if match:
            title = match[1]
            heading = {'title': title, 'anchor': re.sub(r'[^\w\- ]', '', title.lower()).replace(' ', '-')}
        if not line.startswith('<!-- proof-blocker:'): continue
        match = re.fullmatch(r'<!-- proof-blocker: ([\w.]+) -->', line)
        if not match or not heading: raise ValueError('invalid proof blocker marker in overview')
        name = match[1]
        if name in blockers: raise ValueError(f'duplicate proof blocker: {name}')
        blockers[name] = dict(heading)
    return blockers

def read_readiness():
    """Reviewed proof work is maintained once, in overview; it never grants proof status."""
    text = (ROOT / 'docs/overview.md').read_text()
    start, end = '<!-- proof-readiness:start -->', '<!-- proof-readiness:end -->'
    if start not in text and end not in text: return {}
    if text.count(start) != 1 or text.count(end) != 1:
        raise ValueError('invalid proof readiness markers in overview')
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

def build_graph(export, digest):
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
            if dep in proof_owner:
                add(proof_owner[dep], g, 'proof'); continue
            if dep in goals: continue
            row = declarations.get(dep)
            if row: todo.extend(row['refs'])
    return {'version': 1, 'inputSha256': digest, 'links': link_context(digest),
            'counts': dict(Counter(n['status'] for n in nodes)),
            'groups': GROUPS, 'statuses': STATUSES, 'nodes': nodes,
            'edges': [{'from': a, 'to': b, 'kind': k} for a, b, k in sorted(edges)],
            'modules': module_graph(nodes, declarations),
            'acceptance': 'Not a final audit or CI result. Registered and locally checked are distinct from final acceptance.'}

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

def module_mermaid(graph):
    modules = graph['modules']
    indexes = {path: f'm{i}' for i, path in enumerate(modules['nodes'])}
    lines = ['flowchart LR']
    for path, index in indexes.items():
        label = html.escape(path.removeprefix('ZlibF/').removesuffix('.lean'), quote=True)
        lines.append(f'  {index}["{label}"]')
    for dependency, caller in modules['edges']:
        lines.append(f'  {indexes[dependency]} --> {indexes[caller]}')
    for path, index in indexes.items():
        lines.append(f'  click {index} href "{snapshot_url(graph, path)}" "Open module source" _blank')
    return '\n'.join(lines)

def target_anchor(node):
    return 'target-' + re.sub(r'[^a-z0-9]+', '-', node['id'].lower()).strip('-')

def diagram_styles():
    lines = []
    colors = {'registered': ('#dcfce7', '#166534'), 'local': ('#dbeafe', '#1e40af'),
              'open': ('#e5e7eb', '#374151'), 'blocked': ('#fee2e2', '#991b1b')}
    for status, (fill, text) in colors.items():
        lines.append(f'  classDef {status} fill:{fill},color:{text},stroke:{text}')
    return lines

def mermaid(graph):
    indexes = {n['id']: f'n{i}' for i, n in enumerate(graph['nodes'])}
    lines = ['flowchart LR']
    for key, title in GROUPS.items():
        members = [n for n in graph['nodes'] if n['group'] == key]
        if not members: continue
        lines += [f'  subgraph {key}["{title}"]']
        for node in members:
            label = html.escape(node['label'], quote=True)
            if node['blocker']: label += '<br/>Blocked'
            elif node['status'] == 'open' and node.get('scope') == 'public':
                work = node.get('readiness') or {'label': 'Prerequisites unreviewed'}
                label += '<br/>' + html.escape(work['label'], quote=True)
            lines.append(f'    {indexes[node["id"]]}["{label}"]:::{node["status"]}')
        lines.append('  end')
    for edge in graph['edges']:
        arrow = '-->' if edge['kind'] == 'call' else '-.->'
        lines.append(f'  {indexes[edge["from"]]} {arrow} {indexes[edge["to"]]}')
    for node in graph['nodes']:
        # GitHub renders Mermaid on a different host. A relative SVG href resolves
        # against that host, so diagram links use immutable GitHub commit URLs.
        url = target_url(graph, node)
        tooltip = 'Open blocker reason and next step' if node['blocker'] else 'Open target specification'
        lines.append(f'  click {indexes[node["id"]]} href "{url}" "{tooltip}" _blank')
    lines.extend(diagram_styles())
    return '\n'.join(lines)

def summary_mermaid(graph):
    lines = ['flowchart LR']
    for key, title in GROUPS.items():
        members = [n for n in graph['nodes'] if n['group'] == key]
        if not members: continue
        counts = Counter(n['status'] for n in members)
        status = ('blocked' if counts['blocked'] else 'registered' if counts['registered'] == len(members)
                  else 'local' if counts['local'] or counts['registered'] else 'open')
        caption = f"{title}<br/>{len(members)} targets · {counts['registered']} registered · {counts['local']} local"
        if counts['blocked']: caption += f" · {counts['blocked']} blocked"
        lines.append(f'  {key}["{caption}"]:::{status}')
    owners = {n['id']: n['group'] for n in graph['nodes']}
    combined = {}
    for edge in graph['edges']:
        pair = (owners[edge['from']], owners[edge['to']])
        if pair[0] == pair[1]: continue
        if pair not in combined or edge['kind'] == 'call': combined[pair] = edge['kind']
    for (a, b), kind in sorted(combined.items()):
        arrow = '-->' if kind == 'call' else '-.->'
        lines.append(f'  {a} {arrow} {b}')
    for key in GROUPS:
        if any(n['group'] == key for n in graph['nodes']):
            lines.append(f'  click {key} href "{group_url(graph, key)}" "Open specifications" _blank')
    lines.extend(diagram_styles())
    return '\n'.join(lines)

START = '<!-- proof-progress:start -->'
END = '<!-- proof-progress:end -->'

def blocker_index(graph, page='progress.md'):
    groups = defaultdict(list)
    for node in graph['nodes']:
        if node['blocker']: groups[(node['blocker']['anchor'], node['blocker']['title'])].append(node)
    if not groups: return 'No documented blockers in this snapshot.'
    lines = ['| Blocked targets | Reason and next step |', '| --- | --- |']
    for (anchor, title), nodes in sorted(groups.items()):
        targets = ', '.join(f'[{n["label"]}](./{page}#{target_anchor(n)})' for n in nodes)
        lines.append(f'| {targets} | [{title}](./overview.md#{anchor}) |')
    return '\n'.join(lines)

def detail_page(graph, supporting=False):
    page = 'supporting-proofs.md' if supporting else 'progress.md'
    counts = graph['counts']
    meanings = {'registered': '🟩 Exact checked proof listed in the theorem registry.',
                'local': '🟦 Exact checked proof, not yet registered.',
                'open': '⬜ No exact checked proof or documented blocker. Source drafts do not count.',
                'blocked': '🟥 Not proved; a documented obstacle needs resolution. Click for its reason and next step.'}
    rows = '\n'.join(f'| <a id="status-{status}"></a>{title} | {counts.get(status, 0)} | {meanings[status]} |'
                     for status, title in STATUSES.items())
    arrow_key = ('Solid arrows in the module graph show observed references between specification and proof modules.\nDotted arrows are not used in that graph. These are structural references, not a complete proof plan.' if supporting else '''Solid arrows point from a called public entry to its caller, including calls through
translated helpers. Dotted arrows record actual proof or target-definition references.
These are observed references, not assumed callee contracts or a complete proof plan.
Missing arrows do not establish mathematical independence. Cycles are preserved.
Even when every displayed prerequisite is checked, a caller must establish callee
preconditions, compose heap effects and prove its own branches and loops. Gray is not
a restriction on when work can start; internal lemmas may already exist.

Gray public nodes also show reviewed next work from
[Public API proof readiness](overview.md#public-api-proof-readiness).
`Start:` names independent work to begin; `Needs:` names a missing composition result.
Neither label is a proof status or permission to assume a callee contract.
`Prerequisites unreviewed` explicitly leaves readiness unknown.''')
    groups = [(key, title, [n for n in graph['nodes'] if n['group'] == key]) for key, title in GROUPS.items()]
    groups = [(key, title, members) for key, title, members in groups if members]
    group_index = '\n'.join(f'| [{title}](./{page}#group-{key}) | {len(members)} |' for key, title, members in groups)
    md = f'''# {'Supporting proofs' if supporting else 'Public API proof target graph'}

<!-- proof-link-revision: {graph['links']['revision']} -->

[Documentation](README.md) · [Current work and group graph](overview.md) · [{"Public API targets" if supporting else "Supporting proofs"}]({"progress.md" if supporting else "supporting-proofs.md"})

This generated view contains **{len(graph['nodes'])} {'supporting targets' if supporting else 'public API targets'}**.
{'These are internal obligations, byte-address goals and abstract models. They are excluded from the public API progress count.' if supporting else 'The scope is the public API manifest: function contracts, call sequences and initialization domains. Internal obligations and abstract models have a separate supporting page.'}
Each target is from `tests/audit/goals.txt`. Colours report the freshly built
local environment, not final acceptance. A checked theorem must have exactly the target
as its type and use only allowed axioms. Source-only candidates never count as checked.
The numbers count targets, not proof difficulty or percentage of effort.

## Status key

| Status | Targets | Meaning |
| --- | ---: | --- |
{rows}

Registered proofs still need the full audit and CI for final acceptance.
Disallowed axiom dependencies stop generation with an error; they are not a progress state.

{arrow_key}

## Blockers

{blocker_index(graph, page)}

Red marks an explicit blocker recorded in overview, not elapsed time or proof difficulty.
Other targets are not marked red merely because they call a blocked function.

**Why can an isolated node be unfinished?** The public graph omits supporting goals.
The supporting module graph records source references, not a complete proof plan.
No arrows means no displayed link, not that a proof exists or is easy.
Green requires a checked, registered exact proof. See the
[supporting proofs](supporting-proofs.md) and [representation limits](trusted-base.md).

## Clickable index

Diagram links open a fixed GitHub snapshot, `{graph['links']['revision'][:7]}`.
A target opens its specification. Red targets open their blocker;
groups open their specification file or folder. These links survive merges and branch deletion.
Some Markdown viewers disable diagram links; use the ordinary tables in that case.
Table links remain document-relative and follow the branch being viewed on GitHub.
Local previews open the corresponding local documents.

| Group | Targets |
| --- | ---: |
{group_index}

## {'Module dependencies' if supporting else 'Public API targets'}

{'This is a module reference graph, not a graph of assumed callee contracts. A solid arrow A → B means declarations in B reference A, directly or through omitted helper modules. Both definition and type references are included. Module nodes have no proof status; the target table below carries the status colours. A missing edge only means no reference was observed in this compiled snapshot.' if supporting else ''}

```mermaid
{module_mermaid(graph) if supporting else mermaid(graph)}
```

## Proof references

The links below let a reader check the evidence behind each coloured node.
A source-only candidate is not a completed proof. An open target may still have useful
internal lemmas; they do not automatically prove the public target.

'''
    for key, title, members in groups:
        md += f'\n<a id="group-{key}"></a>\n\n### {title}\n\n'
        md += ('| Target statement | State | Contract | Proof evidence |\n| --- | --- | --- | --- |\n' if supporting else
               '| Target statement | State | Contract | Proof evidence | Next proof work |\n| --- | --- | --- | --- | --- |\n')
        for node in members:
            source = '../' + node['source'] + (f"#L{node['line']}" if node['line'] else '')
            label = f'<a id="{target_anchor(node)}"></a>[{node["label"]}]({source})'
            proofs = node['proofs'] or node['candidates']
            evidence = '; '.join(f"[{p['name']}](../{p['source']}" +
                                 (f"#L{p['line']}" if p.get('line') else '') + ')' for p in proofs) or '—'
            if node['candidates']: evidence = 'Unchecked source: ' + evidence
            contract = f'[Contract](../{node["manual"]})' if node['manual'] else 'See target statement'
            if node['blocker']:
                evidence = f'[Blocker: {node["blocker"]["title"]}](./overview.md#{node["blocker"]["anchor"]})'
            state = f'[{STATUSES[node["status"]]}](./{page}#status-{node["status"]})'
            work = node.get('readiness')
            next_work = f"[{work['label']}](./overview.md#{work['anchor']})" if work and node['status'] in {'open', 'blocked'} else ('Prerequisites unreviewed' if node['scope'] == 'public' and node['status'] == 'open' else '—')
            md += f'| {label} | {state} | {contract} | {evidence} |' + ('' if supporting else f' {next_work} |') + '\n'
    md += f'''
## Refresh

Run `python3 scripts/proof-progress.py` from the repository root after proof or registry
updates. It rechecks source hashes, builds the root without downloading cached artifacts,
and inspects exact compiled theorem types. It updates both target pages and only the
marked graph section at the top of overview. `--check` detects stale views.
It never changes a registry, target, proof, lock or verification gate.
Use the [acceptance checks](checking/README.md) for acceptance evidence.
Current work and remaining tasks are maintained only in [overview](overview.md).

Input fingerprint: `{graph['inputSha256']}`.
'''
    return md

def outputs(graph):
    public = select_view(graph, 'public')
    supporting = select_view(graph, 'supporting')
    counts = public['counts']
    block = f'''{START}
## Proof progress graph

**{len(public['nodes'])} public API targets.** Registered proofs: {counts.get('registered', 0)} ·
locally checked but not registered: {counts.get('local', 0)} ·
not proved without a recorded blocker: {counts.get('open', 0)} ·
blocked: {counts.get('blocked', 0)}.
These are local snapshot counts, not final verification or a percentage of effort.

[Open the public API graph and proof references](progress.md).
The scope is the public API manifest, including call sequences and initialization domains.
[Supporting proofs](supporting-proofs.md) lists the other {len(supporting['nodes'])} audit targets
and their module dependencies. They do not change the public API counts.
🟩 **Registered proof** · 🟦 **Locally checked, not registered** · ⬜ **Not proved** · 🟥 **Blocked**.
Red groups contain a blocked target. Other mixed groups use blue when they contain
checked results; counts show what remains. Work on other targets can continue.
Solid arrows show calls from the called entry to its caller. Dotted arrows show
proof or target-definition references. [Status details](progress.md#status-key).
Final acceptance still requires the full audit and CI on a named commit.

### Blockers

{blocker_index(public)}

```mermaid
{summary_mermaid(public)}
```

Arrows aggregate actual implementation calls and proof/definition references.
An isolated node has no displayed links; it still needs its own proof. Helper and runtime
dependencies are detailed in [Public API proof readiness](./overview.md#public-api-proof-readiness).
Green requires checked, registered proofs for every
target in a group. Readiness labels identify reviewed next work without changing proof
status. Unreviewed prerequisites remain explicit. See the [representation limits](./trusted-base.md).

Click a group to open its specifications. If diagram links are disabled, use the
[group index](progress.md#clickable-index). [The detailed graph](progress.md) shows every
public API target separately, with links to its contract, statement and proof evidence.
Diagram links use the fixed GitHub snapshot `{graph['links']['revision'][:7]}` and survive merges
and branch deletion. Table links remain relative to this document.
Refresh with `python3 scripts/proof-progress.py` after proof changes.
{END}'''
    overview = (ROOT / 'docs/overview.md').read_text()
    if START in overview:
        if overview.count(START) != 1 or overview.count(END) != 1: raise ValueError('invalid graph markers')
        before, rest = overview.split(START, 1)
        _, after = rest.split(END, 1)
        overview = before + block + after
    else:
        marker = '## Recorded checkpoint'
        if marker not in overview: raise ValueError('overview insertion point missing')
        overview = overview.replace(marker, block + '\n\n' + marker, 1)
    return {'docs/progress.md': detail_page(public),
            'docs/supporting-proofs.md': detail_page(supporting, supporting=True),
            'docs/overview.md': overview}

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
    graph = build_graph(export, digest)
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
            # Re-read overview under the lock, preserving other workers' new prose.
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
