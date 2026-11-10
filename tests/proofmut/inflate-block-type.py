#!/usr/bin/env python3
"""Check actual TYPE/TYPEDO changes against their execution proofs.

Only in the temporary build, omit older raw end-to-end proofs that also
inspect TYPE dispatch. The unmutated isolated baseline must still check.
No assumptions replace those proofs, and the checkout is unchanged.
"""
from pathlib import Path
import os
import re
import shutil
import subprocess
import tempfile


def main():
    root = Path(__file__).resolve().parents[2]
    source = Path('ZlibF/Zlib/inflate.c.lean')
    cut = Path('ZlibF/Proof/inflate.c.main.type.lean')
    boundary = Path('ZlibF/Proof/inflate.c.block-type.lean')
    original = (root / source).read_text()
    proof = (root / cut).read_text()
    variants = (
        ('wrong-dispatch', 'dispatch', 'then inflate_TYPE c', 'then inflate_HEAD c', 'inflate_dispatch_block_type'),
        ('ignored-flush', 'type', 'if c.flush == Z_BLOCK || c.flush == Z_TREES then', 'if false then', 'inflate_TYPE_leave'),
        ('wrong-final-mode', 'typedo', 'setMode c.st CHECK', 'setMode c.st DONE', 'inflate_TYPEDO_last'),
        ('short-header', 'typedo', 'NEEDBITS 3', 'NEEDBITS 2', 'inflate_TYPEDO_wait'),
        ('stored-becomes-table', 'tail', 'setMode c.st STORED', 'setMode c.st TABLE', 'typedoTail_stored'),
        ('wrong-header-drop', 'tail', 'DROPBITS 2', 'DROPBITS 1', 'typedoTail_stored'),
    )
    env = os.environ.copy()
    env['LC_ALL'] = 'C'
    target = 'ZlibF.Proof.«inflate.c.head-default-state»'

    def build(where):
        return subprocess.run(['lake', 'build', target], cwd=where, env=env, text=True,
                              stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=600)

    with tempfile.TemporaryDirectory(prefix='inflate-block-type-') as directory:
        scratch = Path(directory)
        for file in ('lakefile.toml', 'lean-toolchain'):
            shutil.copy2(root / file, scratch / file)
        shutil.copytree(root / 'ZlibF', scratch / 'ZlibF')
        shutil.copytree(root / '.lake', scratch / '.lake', ignore=shutil.ignore_patterns('*.tmp.*', 'Index.*'))
        stored = scratch / 'ZlibF/Proof/inflate.c.stored-call.lean'
        text = stored.read_text()
        a = text.rindex('/--', 0, text.index('theorem inflate_leave_raw_finish_done'))
        b = text.rindex('/--', 0, text.index('theorem LOAD_run'))
        c = text.rindex('/--', 0, text.index('theorem inflate_run_raw_copy'))
        stored.write_text(text[:a] + text[b:c] + '\nend Zlib.Inflate.Proofs\n')
        baseline = build(scratch)
        if baseline.returncode:
            raise RuntimeError('baseline failed:\n' + baseline.stdout)
        print('baseline: complete actual TYPE/TYPEDO boundaries check', flush=True)
        for label, stage, old, new, theorem in variants:
            if stage == 'dispatch':
                a = original.index('def inflate_dispatch (')
                b = original.index('def inflate_run (', a)
            elif stage == 'type':
                a = original.index('def inflate_TYPE (')
                b = original.index('def inflate_DICT (', a)
            else:
                a = original.index('def inflate_TYPEDO (')
                b = original.index('def inflate_TYPE (', a)
            section = original[a:b]
            lines = section.splitlines(keepends=True)
            hits = [i for i, line in enumerate(lines) if not line.lstrip().startswith('--') and old in line]
            required = 2 if label == 'wrong-header-drop' else 1
            if len(hits) != required:
                raise RuntimeError('ambiguous source mutation: ' + label)
            for i in hits:
                lines[i] = lines[i].replace(old, new)
            (scratch / source).write_text(original[:a] + ''.join(lines) + original[b:])
            changed = proof
            if stage == 'tail':
                a = proof.index('def typedoTail (')
                b = proof.index('/-- `case TYPEDO:` with the header', a)
                section = proof[a:b]
                if section.count(old) != required:
                    raise RuntimeError('ambiguous literal suffix: ' + label)
                changed = proof[:a] + section.replace(old, new) + proof[b:]
            (scratch / cut).write_text(changed)
            result = build(scratch)
            expected = boundary if stage == 'dispatch' else cut
            text = (root / boundary).read_text() if stage == 'dispatch' else changed
            begin = text.index('theorem ' + theorem + ' ')
            tail = text[begin:]
            end = re.search(r'\n(?:theorem|/--|end)\b', tail)
            low = text[:begin].count('\n') + 1
            high = len(text.splitlines()) if end is None else low + tail[:end.start()].count('\n')
            first = re.search(r'^error: ([^\n]+)', result.stdout, re.MULTILINE)
            hit = re.match(re.escape(str(expected)) + r':(\d+):', first.group(1)) if first else None
            exhausted = any(word in result.stdout.lower() for word in (
                'maximum recursion depth', 'maximum number of heartbeats', 'deterministic timeout'))
            if result.returncode == 0 or hit is None or not low <= int(hit.group(1)) <= high or exhausted:
                raise RuntimeError(label + ' lacks a direct non-resource proof failure:\n' + result.stdout)
            print('KILLED ' + label + ': ' + first.group(1), flush=True)
        print('PASS: six actual block-type mutants; no resource failures', flush=True)


if __name__ == '__main__':
    main()
