#!/usr/bin/env python3
"""Compare every execution-observation row without remapping failure indices.

The NULL-destination/zero-capacity rows are execution observations, not a
claim that the C NULL-NULL pointer subtraction has defined standard semantics.
Wrapper NULL-scalar faults are checked separately from the compared rows.
"""
import sys
from pathlib import Path

FUNCTIONS = ('compress2_z', 'compress2', 'compress_z', 'compress')
FAILURES = ('none', '0', '1', '2', '3', '4', '5', '6')


def expected_keys():
    keys = []
    for fn in FUNCTIONS:
        for case in ('normal', 'empty'):
            keys.extend((case, fn, k) for k in FAILURES)
        keys += [('nullsrc', fn, 'none'), ('nulldest_pos', fn, 'none')]
        keys.extend(('nulldest_zero', fn, k) for k in FAILURES)
        if fn in ('compress2_z', 'compress2'):
            keys.append(('badlevel', fn, 'none'))
        if fn in ('compress2_z', 'compress_z'):
            keys.append(('nulllen', fn, 'none'))
    return keys


def load(path, c_side=False):
    rows, unc, ub, comments = [], [], [], []
    for line in Path(path).read_text().splitlines():
        if line.startswith('ROW '):
            data = dict(token.split('=', 1) for token in line.split()[1:])
            if set(data) != {'case', 'fn', 'fail', 'rc', 'destLen', 'out', 'live', 'allocs'}:
                raise ValueError(f'invalid row fields: {line}')
            rows.append((line, data))
        elif line.startswith('UNCROW '):
            data = dict(token.split('=', 1) for token in line.split()[1:])
            if set(data) != {'case', 'fail', 'rc', 'destLen', 'sourceLen', 'out', 'live', 'allocs'}:
                raise ValueError(f'invalid uncompress row fields: {line}')
            unc.append((line, data))
        elif line.startswith('UBROW ') and not c_side:
            ub.append(line)
        elif line.startswith('# UB skipped: ') and c_side:
            comments.append(line)
        else:
            raise ValueError(f'unexpected output, not discarded: {line!r}')
    keys = [(d['case'], d['fn'], d['fail']) for _, d in rows]
    if keys != expected_keys():
        raise ValueError(f'{path}: expected all 108 rows in exact matrix order, got {len(rows)}')
    if len(unc) != 1 or (unc[0][1]['case'], unc[0][1]['fail']) != ('prefix5', '1'):
        raise ValueError(f'{path}: missing or wrong uncompress observation')
    wrappers = ('compress2', 'compress')
    if c_side:
        expected = [f'# UB skipped: case=nulllen fn={fn}' for fn in wrappers]
        if comments != expected:
            raise ValueError(f'{path}: incorrect C UB exclusions')
    else:
        if len(ub) != 2 or any(
                not line.startswith(f'UBROW case=nulllen fn={fn} fail=none result=FAULT ')
                for line, fn in zip(ub, wrappers)):
            raise ValueError(f'{path}: missing actual Lean wrapper-fault observations')
    return rows, unc, ub


def compare(c_path, current_path, old_path, report_path):
    c, cu, _ = load(c_path, True)
    current, current_u, _ = load(current_path)
    old, old_u, _ = load(old_path)
    report = []
    current_diffs, old_diffs = [], []
    for index, ((a, _), (b, _)) in enumerate(zip(c + cu, current + current_u), 1):
        if a != b:
            current_diffs.append((index, a, b))
    for index, ((a, _), (b, _)) in enumerate(zip(c + cu, old + old_u), 1):
        if a != b:
            old_diffs.append((index, a, b))
    for label, diffs in [('current', current_diffs), ('old', old_diffs)]:
        report.append(f'{label}: {len(diffs)} differences across ALL 109 compared rows')
        for index, a, b in diffs:
            report += [f'DIFFERENCE {label} row {index}', f'C    {a}', f'Lean {b}']
    errors = []
    if current_diffs:
        errors.append('current execution observations differ')
    for label, rows in [('C', c + cu), ('current', current + current_u)]:
        for line, data in rows:
            if data['live'] != '0':
                errors.append(f'{label}: live allocations remain: {line}')
            if len(data['out']) != (512 if data['case'] == 'prefix5' else 128):
                errors.append(f'{label}: full output buffer missing: {line}')
    for fn in FUNCTIONS:
        ci = next(d for _, d in c if (d['case'], d['fn'], d['fail']) == ('normal', fn, '0'))
        oi = next(d for _, d in old if (d['case'], d['fn'], d['fail']) == ('normal', fn, '0'))
        if (ci['rc'], ci['destLen'], ci['allocs'], ci['out']) != ('-4', '0', '1', 'a5' * 64):
            errors.append(f'{fn}: C first-malloc-failure signature is wrong')
        if oi['rc'] != 'FAULT':
            errors.append(f'{fn}: old translation did not expose the fail0 fault')
    if [x[0] for x in cu] != [x[0] for x in old_u]:
        errors.append('old-control uncompress observation unexpectedly differs')
    u = cu[0][1]
    if (u['rc'], u['destLen'], u['sourceLen'], u['allocs'], u['live'], u['out']) != (
            '-4', '1', '5', '2', '0', '41' + 'a5' * 255):
        errors.append('window-allocation failure did not retain the one-byte output')
    if not old_diffs:
        errors.append('old translation unexpectedly matched')
    report += ['ERROR: ' + message for message in errors]
    if not errors:
        report += ['PASS: current 109 exact observations match; all live counts zero;',
                   'old control fails at normal fail0 for every compress entry, no index remapping.']
    text = '\n'.join(report) + '\n'
    Path(report_path).write_text(text)
    print(text, end='')
    return bool(errors)


if __name__ == '__main__':
    try:
        raise SystemExit(compare(*sys.argv[1:5]))
    except (ValueError, OSError, TypeError) as error:
        print(f'FAIL: {error}', file=sys.stderr)
        raise SystemExit(2)
