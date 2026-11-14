#!/usr/bin/env python3
"""Check the layers of the specification (docs/design/safety-functional-split.md).

A module under ZlibF/Spec/Safety/ or ZlibF/Spec/Public/ must not import, even transitively, a
module under ZlibF/Spec/Functional/ or one of the compatibility modules that re-export it
(ZlibF/Spec/Api*, ZlibF/Spec/Format*). Then reading Spec/Safety and what it imports tells a reader
the whole current target.

ALLOWED lists the import edges that are still to be removed, each with its reason. The list may
only shrink: an entry whose edge no longer exists is an error, so it is deleted when its edge goes.
"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

# (importer, imported): reason. Each edge is removed by a later step of the split.
ALLOWED = {
    ('ZlibF.Spec.Public.GzState', 'ZlibF.Spec.Api.Gz'):
        'gzip step: GzState uses the gz mode decoder (Api.GzMode, gzMode?) and GzLooksGzip',
}


def module_path(name):
    return ROOT / (name.replace('.', '/').replace('«', '').replace('»', '') + '.lean')


def module_name(path):
    return '.'.join(path.relative_to(ROOT).with_suffix('').parts)


def imports(name):
    path = module_path(name)
    if not path.is_file():
        return []
    found = []
    for line in path.read_text().splitlines():
        match = re.match(r'import\s+(\S+)', line)
        if match:
            found.append(match.group(1))
        elif line.strip() and not line.startswith('--') and not line.startswith('prelude'):
            break
    return [m for m in found if m.startswith('ZlibF.')]


def functional(name):
    return (name.startswith('ZlibF.Spec.Functional.') or name == 'ZlibF.Spec.Functional'
            or name in ('ZlibF.Spec.Api', 'ZlibF.Spec.Format')
            or name.startswith('ZlibF.Spec.Api.') or name.startswith('ZlibF.Spec.Format.'))


def layered(name):
    return name.startswith('ZlibF.Spec.Safety.') or name.startswith('ZlibF.Spec.Public.')


def main():
    errors = []
    for (src, dst), reason in ALLOWED.items():
        if dst not in imports(src):
            errors.append(f'allowlisted edge {src} -> {dst} no longer exists: delete it ({reason})')
    roots = sorted(module_name(p) for d in ('Safety', 'Public')
                   for p in (ROOT / 'ZlibF/Spec' / d).rglob('*.lean'))
    for root in roots:
        parent = {root: None}
        stack = [root]
        while stack:
            name = stack.pop()
            for child in imports(name):
                if (name, child) in ALLOWED or child in parent:
                    continue
                parent[child] = name
                stack.append(child)
        for name in sorted(n for n in parent if functional(n)):
            chain = [name]
            while parent[chain[-1]] is not None:
                chain.append(parent[chain[-1]])
            errors.append(f'{root} imports functional {name}: ' + ' <- '.join(chain))
            break
    if errors:
        print('Specification layer check failed (docs/design/safety-functional-split.md):')
        for error in errors:
            print('  ' + error)
        return 1
    print(f'specification layers: {len(roots)} safety and common modules import no functional module')
    return 0


if __name__ == '__main__':
    sys.exit(main())
