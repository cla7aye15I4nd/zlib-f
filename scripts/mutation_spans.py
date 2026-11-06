"""Read-only proof-mutant span guard. Parse both files using an approved Span.lean.
Never fall back to regex or to candidate-provided declaration range extensions.
"""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]


def parse(path):
    env = dict(os.environ)
    # Prevent a candidate worktree from shadowing trusted parser imports.
    env.pop('LEAN_PATH', None)
    env.pop('LEAN_SRC_PATH', None)
    env['ELAN_TOOLCHAIN'] = (ROOT / 'lean-toolchain').read_text().strip()
    binary = subprocess.check_output(['elan', 'which', 'lean'], cwd=ROOT, env=env, text=True).strip()
    with tempfile.TemporaryDirectory(prefix='trusted-command-parser-') as directory:
        result = subprocess.run([binary, '--run', str(ROOT / 'tests/audit/DeclarationSpan.lean'),
                                 str(Path(path).resolve())], cwd=directory, env=env,
                                capture_output=True, text=True, timeout=60)
    if result.returncode:
        raise ValueError('trusted parser rejected source: ' + result.stdout + result.stderr)
    return json.loads(result.stdout)


def unique(document, syntax_name):
    matches = [c for c in document['commands'] if c['declaration'] and c['declaration']['syntaxName'] == syntax_name]
    if len(matches) != 1 or not matches[0]['declaration']['supportedBody']:
        raise ValueError('target must be one unique top-level named := declaration; unsupported forms reject')
    return matches[0]


def check(original, mutant, syntax_name):
    old, new = Path(original).read_bytes(), Path(mutant).read_bytes()
    a, b = parse(original), parse(mutant)
    x, y = unique(a, syntax_name), unique(b, syntax_name)
    ob, oe = x['declaration']['body']
    nb, ne = y['declaration']['body']
    if ob != nb or old[:ob] != new[:nb] or old[oe:] != new[ne:]:
        raise ValueError('change is outside the actual target body or changes its signature/suffix')
    if old[ob:oe] == new[nb:ne]:
        raise ValueError('target body unchanged')
    # The outer body must still occupy the entire replacement; command injection
    # changes the parsed body endpoint and therefore cannot pass the suffix check.
    delta = len(new) - len(old)
    if len(a['commands']) != len(b['commands']):
        raise ValueError('top-level command inventory changed')
    for ca, cb in zip(a['commands'], b['commands']):
        if ca is x:
            if cb is not y or ca['kind'] != cb['kind']:
                raise ValueError('target command identity changed')
            if cb['span'] != [ca['span'][0], ca['span'][1] + delta]:
                raise ValueError('target body escaped its declaration')
            continue
        shift = delta if ca['span'][0] >= oe else 0
        expected = [n + shift for n in ca['span']]
        if ca['kind'] != cb['kind'] or cb['span'] != expected:
            raise ValueError('another command changed shape or position')
        if old[slice(*ca['span'])] != new[slice(*cb['span'])]:
            raise ValueError('another command changed')
    return {'accepted': True, 'syntaxName': syntax_name, 'oldBody': [ob, oe], 'newBody': [nb, ne]}


if __name__ == '__main__':
    try:
        print(json.dumps(check(*sys.argv[1:]), sort_keys=True))
    except (ValueError, subprocess.TimeoutExpired) as error:
        print(str(error), file=sys.stderr)
        sys.exit(1)
