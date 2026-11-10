#!/usr/bin/env python3
"""Require direct failures for actual inf_leave counter and return mutants.

Each literal source cut is synchronized. Expected counter values and return
relations stay fixed. The same isolated baseline omits the overlapping older
raw-call proof, without replacing any proof with an assumption.
"""
from pathlib import Path
import os
import sys
import re
import shutil
import subprocess
import tempfile


def replace_definition(text, begin, end, old, new):
    a = text.index(begin)
    b = text.index(end, a)
    part = text[a:b]
    if part.count(old) != 1:
        raise RuntimeError('ambiguous literal source mutation: ' + begin)
    return text[:a] + part.replace(old, new) + text[b:]


def main():
    root = Path(__file__).resolve().parents[2]
    paths = (Path('ZlibF/Zlib/inflate.c.lean'),
             Path('ZlibF/Proof/inflate.c.leave-restore.lean'),
             Path('ZlibF/Proof/inflate.c.leave-finalize.lean'))
    originals = [(root / p).read_text() for p in paths]
    variants = (
        ('counter-wrong-input', 'total_in := z.total_in + in_.toUInt64',
         'total_in := z.total_in + (in_ + 1).toUInt64', 'counters', 'leaveCounters_run'),
        ('counter-drop-output', 'total_out := z.total_out + out_.toUInt64',
         'total_out := z.total_out', 'counters', 'leaveCounters_run'),
        ('counter-drop-private-output', 'total := s.total + out_.toUInt64',
         'total := s.total', 'counters', 'leaveCounters_run'),
        ('datatype-wrong-value', 'data_type := dt', 'data_type := dt + 1', 'return', 'leaveReturn_run'),
        ('return-wrong-stall', 'then ret := Z_BUF_ERROR', 'then ret := Z_OK', 'return', 'leaveReturn_run'),
        ('return-wrong-progress', 'let mut ret := l.ret', 'let mut ret := Z_OK', 'return', 'leaveReturn_run'),
    )
    env = os.environ.copy()
    env['LC_ALL'] = 'C'
    state_mode = '--default-state' in sys.argv[1:]
    result_mode = '--result-modes' in sys.argv[1:]
    if state_mode:
        variants = tuple((label, 'total := s.total + out_.toUInt64',
                          'total := s.total + out_.toUInt64, ' + update,
                          'counters', 'leaveCounters_run') for label, update in (
            ('state-wrong-requested-bits', 'reqbits := 0'),
            ('state-wrong-requested-wrapper', 'reqwrap := 0'),
            ('state-enable-gzip', 'wrap := 6'),
            ('state-corrupt-header-flags', 'flags := 512'),
            ('state-register-header', 'head := some (.tab 0)'),
        ))
    target = ('ZlibF.Proof.«inflate.c.default-mode-result»' if result_mode else
              'ZlibF.Proof.«inflate.c.default-public-state»' if state_mode else
              'ZlibF.Proof.«inflate.c.leave-finalize»')

    def run(directory, selected=None):
        return subprocess.run(['lake', 'build', selected or target], cwd=directory, env=env, text=True,
                              stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=600)

    with tempfile.TemporaryDirectory(prefix='inflate-leave-finalize-') as directory:
        scratch = Path(directory)
        for name in ('lakefile.toml', 'lean-toolchain'):
            shutil.copy2(root / name, scratch / name)
        shutil.copytree(root / 'ZlibF', scratch / 'ZlibF')
        shutil.copytree(root / '.lake', scratch / '.lake', ignore=shutil.ignore_patterns('*.tmp.*', 'Index.*'))
        stored = scratch / 'ZlibF/Proof/inflate.c.stored-call.lean'
        text = stored.read_text()
        a = text.rindex('/--', 0, text.index('theorem inflate_leave_raw_finish_done'))
        b = text.rindex('/--', 0, text.index('theorem LOAD_run'))
        c = text.rindex('/--', 0, text.index('theorem inflate_run_raw_copy'))
        stored.write_text(text[:a] + text[b:c] + '\nend Zlib.Inflate.Proofs\n')
        baseline = run(scratch)
        if baseline.returncode:
            raise RuntimeError('isolated baseline failed:\n' + baseline.stdout)
        print('baseline: ' + ('complete public progress and mode-result checks' if result_mode else
                              'complete default public state preservation checks' if state_mode else
                              'complete actual no-window return and state preservation checks'), flush=True)
        for label, old, new, stage, theorem in variants:
            src = replace_definition(originals[0], 'def inflate_leave (', '/-- `int ZEXPORT inflate(', old, new)
            restore = replace_definition(originals[1], 'def leaveAfterRestore (', '/-- Stream fields', old, new)
            finalize = replace_definition(originals[2], 'def leaveFinalize (', '/-- The final data_type', old, new)
            if stage == 'counters':
                finalize = replace_definition(finalize, 'def leaveCounters (', '/-- The actual optional', old, new)
            else:
                finalize = replace_definition(finalize, 'def leaveReturn (', '/-- The two actual counter', old, new)
            for path, text in zip(paths, (src, restore, finalize)):
                (scratch / path).write_text(text)
            # Check the affected source callee first. The positive baseline above
            # checks its complete public caller; an unrelated parallel rebuild
            # cannot replace the required direct callee failure.
            result = run(scratch, 'ZlibF.Proof.«inflate.c.leave-finalize»' if state_mode or result_mode else None)
            first = re.search(r'^error: ([^\n]+)', result.stdout, re.MULTILINE)
            hit = re.match(re.escape(str(paths[2])) + r':(\d+):', first.group(1)) if first else None
            a = finalize.index('theorem ' + theorem + ' ')
            rest = finalize[a:]
            end = re.search(r'\n(?:theorem|/--|end)\b', rest)
            low = finalize[:a].count('\n') + 1
            high = len(finalize.splitlines()) if end is None else low + rest[:end.start()].count('\n')
            exhausted = any(term in result.stdout.lower() for term in (
                'maximum recursion depth', 'maximum number of heartbeats', 'deterministic timeout'))
            if result.returncode == 0 or hit is None or not low <= int(hit.group(1)) <= high or exhausted:
                raise RuntimeError(label + ' lacks a direct non-resource proof failure:\n' + result.stdout)
            print('KILLED ' + label + ': ' + first.group(1), flush=True)
        print(f'PASS: {len(variants)} actual ' + ('default-state' if state_mode else 'counter/metadata/return') +
              ' mutants; no resource failures', flush=True)


if __name__ == '__main__':
    main()
