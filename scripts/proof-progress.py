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
import re
import shutil
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parents[1]
GROUPS = {'queries': 'Library queries', 'checksums': 'Checksums', 'inflate': 'Inflate streams',
          'deflate': 'Deflate streams', 'back': 'Callback decoding', 'gzip': 'Gzip files',
          'buffers': 'Whole-buffer operations', 'models': 'Format and API models',
          'lifecycle': 'Lifecycles and call sequences'}
STATUSES = {'registered': 'Registered proof', 'local': 'Locally checked', 'open': 'Not proved'}

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
    return digest.hexdigest()

def group(name):
    short = name.rsplit('.', 1)[-1]
    if name.startswith('ZlibF.Spec.Api.'): return 'models'
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
    manifest = json.loads((ROOT / 'tests/audit/public-api.json').read_text())
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
        nodes.append({'id': g, 'label': g.rsplit('.', 1)[-1], 'group': group(g), 'status': status,
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
    return {'version': 1, 'inputSha256': digest, 'counts': dict(Counter(n['status'] for n in nodes)),
            'groups': GROUPS, 'statuses': STATUSES, 'nodes': nodes,
            'edges': [{'from': a, 'to': b, 'kind': k} for a, b, k in sorted(edges)],
            'acceptance': 'Not a final audit or CI result. Registered and locally checked are distinct from final acceptance.'}

def target_anchor(node):
    return 'target-' + re.sub(r'[^a-z0-9]+', '-', node['id'].lower()).strip('-')

def diagram_styles():
    lines = []
    colors = {'registered': ('#dcfce7', '#166534'), 'local': ('#dbeafe', '#1e40af'),
              'open': ('#e5e7eb', '#374151')}
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
            lines.append(f'    {indexes[node["id"]]}["{label}"]:::{node["status"]}')
        lines.append('  end')
    for edge in graph['edges']:
        arrow = '-->' if edge['kind'] == 'call' else '-.->'
        lines.append(f'  {indexes[edge["from"]]} {arrow} {indexes[edge["to"]]}')
    for node in graph['nodes']:
        lines.append(f'  click {indexes[node["id"]]} href "#{target_anchor(node)}" "Open target and proof references"')
    lines.extend(diagram_styles())
    return '\n'.join(lines)

def summary_mermaid(graph):
    lines = ['flowchart LR']
    for key, title in GROUPS.items():
        members = [n for n in graph['nodes'] if n['group'] == key]
        if not members: continue
        counts = Counter(n['status'] for n in members)
        status = ('registered' if counts['registered'] == len(members)
                  else 'local' if counts['local'] or counts['registered'] else 'open')
        caption = f"{title}<br/>{len(members)} targets · {counts['registered']} registered · {counts['local']} local"
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
            lines.append(f'  click {key} href "progress.md#group-{key}" "Open group index"')
    lines.extend(diagram_styles())
    return '\n'.join(lines)

START = '<!-- proof-progress:start -->'
END = '<!-- proof-progress:end -->'

def outputs(graph):
    counts = graph['counts']
    meanings = {'registered': '🟩 Exact checked proof listed in the theorem registry.',
                'local': '🟦 Exact checked proof, not yet registered.',
                'open': '⬜ No exact checked proof found. Source drafts do not count.'}
    rows = '\n'.join(f'| <a id="status-{status}"></a>{title} | {counts.get(status, 0)} | {meanings[status]} |'
                     for status, title in STATUSES.items())
    groups = [(key, title, [n for n in graph['nodes'] if n['group'] == key]) for key, title in GROUPS.items()]
    groups = [(key, title, members) for key, title, members in groups if members]
    group_index = '\n'.join(f'| [{title}](#group-{key}) | {len(members)} |' for key, title, members in groups)
    md = f'''# Proof target graph

[Documentation](README.md) · [Current work and group graph](overview.md)

This generated diagram contains **all {len(graph['nodes'])} registered targets**.
Each node is one target from `tests/audit/goals.txt`. Colours report the freshly built
local environment, not final acceptance. A checked theorem must have exactly the target
as its type and use only allowed axioms. Source-only candidates never count as checked.
The numbers count targets, not proof difficulty or percentage of effort.

## Status key

| Status | Targets | Meaning |
| --- | ---: | --- |
{rows}

Registered proofs still need the full audit and CI for final acceptance.
Disallowed axiom dependencies stop generation with an error; they are not a progress state.

Solid arrows point from a called public entry to its caller, including calls through
translated helpers. Dotted arrows record actual proof or target-definition references.
These are observed references, not assumed callee contracts or a complete proof plan.
Missing arrows do not establish mathematical independence. Cycles are preserved.

**Why can an isolated node be unfinished?** Only links between registered targets are
drawn. Runtime, helper and mathematical dependencies outside that set are hidden.
Future proof dependencies may also be unknown. No arrows means no displayed link,
not that a proof exists or is easy. Green requires a checked, registered exact proof.
Arrows do not prescribe when work can start. Shared model issues can block an isolated
target; see the [CRC address-model blocker](overview.md#crc-address-model).

## Clickable index

Click a target in the diagram to reach its entry below. Click a group in the overview
diagram to reach its group index. Some Markdown viewers disable diagram links; the
ordinary links and tables here provide the same navigation.

| Group | Targets |
| --- | ---: |
{group_index}

## All targets

```mermaid
{mermaid(graph)}
```

## Proof references

The links below let a reader check the evidence behind each coloured node.
A source-only candidate is not a completed proof. An open target may still have useful
internal lemmas; they do not automatically prove the public target.

'''
    for key, title, members in groups:
        md += f'\n<a id="group-{key}"></a>\n\n### {title}\n\n'
        md += '| Target statement | State | Contract | Proof evidence |\n| --- | --- | --- | --- |\n'
        for node in members:
            source = '../' + node['source'] + (f"#L{node['line']}" if node['line'] else '')
            label = f'<a id="{target_anchor(node)}"></a>[{node["label"]}]({source})'
            proofs = node['proofs'] or node['candidates']
            evidence = '; '.join(f"[{p['name']}](../{p['source']}" +
                                 (f"#L{p['line']}" if p.get('line') else '') + ')' for p in proofs) or '—'
            if node['candidates']: evidence = 'Unchecked source: ' + evidence
            contract = f'[Contract](../{node["manual"]})' if node['manual'] else 'See target statement'
            state = f'[{STATUSES[node["status"]]}](#status-{node["status"]})'
            md += f'| {label} | {state} | {contract} | {evidence} |\n'
    md += f'''
## Refresh

Run `python3 scripts/proof-progress.py` from the repository root after proof or registry
updates. It rechecks source hashes, builds the root without downloading cached artifacts,
and inspects exact compiled theorem types. It updates this page
and only the marked graph section at the top of overview. `--check` detects stale views.
It never changes a registry, target, proof, lock or verification gate.
Use the [acceptance checks](checking/README.md) for acceptance evidence.
Current work and remaining tasks are maintained only in [overview](overview.md).

Input fingerprint: `{graph['inputSha256']}`.
'''
    block = f'''{START}
## Proof progress graph

**{len(graph['nodes'])} registered targets.** Registered proofs: {counts.get('registered', 0)} ·
locally checked but not registered: {counts.get('local', 0)} ·
not proved: {counts.get('open', 0)}.
These are local snapshot counts, not final verification or a percentage of effort.

[Open the complete coloured graph and proof references](progress.md).
🟩 **Registered proof** · 🟦 **Locally checked, not registered** · ⬜ **Not proved**.
A mixed group uses blue if it has checked results; its counts show what remains.
Solid arrows show calls from the called entry to its caller. Dotted arrows show
proof or target-definition references. [Status details](progress.md#status-key).
Final acceptance still requires the full audit and CI on a named commit.

```mermaid
{summary_mermaid(graph)}
```

Arrows aggregate actual implementation calls and proof/definition references.
An isolated node has no displayed links; it still needs its own proof. Helper and runtime
dependencies are outside this graph. Green requires checked, registered proofs for every
target in a group. Arrows do not prescribe when work can start; shared model issues can
still block a target. See the [CRC address-model blocker](#crc-address-model).

Click a group to open its target index. If diagram links are disabled, use the
[group index](progress.md#clickable-index). [The detailed graph](progress.md) shows every
registered target separately, with links to its contract, statement and proof evidence.
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
    return {'docs/progress.md': md, 'docs/overview.md': overview}

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
