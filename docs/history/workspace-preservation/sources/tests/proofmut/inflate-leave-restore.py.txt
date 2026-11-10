#!/usr/bin/env python3
"""Check actual RESTORE and Adler dispatch mutations with direct proof errors.

The isolated baseline removes earlier raw-call and block-only checksum
proofs so that rejection belongs to the new generic execution proofs.
No checkout proof or registry is changed or replaced by an assumption.
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
    restore = Path('ZlibF/Proof/inflate.c.leave-restore.lean')
    checksum = Path('ZlibF/Proof/inflate.c.checksum-view.lean')
    original = (root / source).read_text()
    proof = (root / restore).read_text()
    env = os.environ.copy()
    env['LC_ALL'] = 'C'
    target = 'ZlibF.Proof.«inflate.c.leave-finalize»'
    cases = [
        ('restore-output-pointer', 'next_out := l.put', 'next_out := l.next', restore, 'leaveRestore_run'),
        ('restore-input-count', 'avail_in := l.have_', 'avail_in := l.have_ - 1', restore, 'leaveRestore_run'),
        ('restore-held-bits', 'hold := l.hold', 'hold := l.hold + 1', restore, 'leaveRestore_run'),
        ('restore-bit-count', 'bits := l.bits', 'bits := l.bits + 1', restore, 'leaveRestore_run'),
        ('checksum-wrong-wrapper', 'if (← rdS st (·.flags)) != 0 then crc32 check buf len else adler32 check buf len',
         'if (← rdS st (·.flags)) == 0 then crc32 check buf len else adler32 check buf len', checksum, 'UPDATE_CHECK_zlib_view'),
        ('checksum-wrong-length', 'else adler32 check buf len', 'else adler32 check buf (len + 1)', checksum, 'UPDATE_CHECK_zlib_view'),
        ('checksum-wrong-seed', 'else adler32 check buf len', 'else adler32 (check + 1) buf len', checksum, 'UPDATE_CHECK_zlib_view'),
    ]

    def run(scratch):
        return subprocess.run(['lake', 'build', target], cwd=scratch, env=env, text=True,
                              stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=600)

    with tempfile.TemporaryDirectory(prefix='inflate-leave-restore-') as directory:
        scratch = Path(directory)
        for name in ('lakefile.toml', 'lean-toolchain'):
            shutil.copy2(root / name, scratch / name)
        shutil.copytree(root / 'ZlibF', scratch / 'ZlibF')
        shutil.copytree(root / '.lake', scratch / '.lake', ignore=shutil.ignore_patterns('*.tmp.*'))
        stored = scratch / 'ZlibF/Proof/inflate.c.stored-call.lean'
        text = stored.read_text()
        a = text.rindex('/--', 0, text.index('theorem inflate_leave_raw_finish_done'))
        b = text.rindex('/--', 0, text.index('theorem LOAD_run'))
        c = text.rindex('/--', 0, text.index('theorem inflate_run_raw_copy'))
        stored.write_text(text[:a] + text[b:c] + '\nend Zlib.Inflate.Proofs\n')
        baseline = run(scratch)
        if baseline.returncode:
            raise RuntimeError('unmutated baseline failed:\n' + baseline.stdout)
        print('baseline: actual RESTORE and generic Adler update check', flush=True)
        for label, old, new, file, theorem in cases:
            if file == restore:
                begin = original.index('def inflate_leave (')
                end = original.index('/-- `int ZEXPORT inflate(', begin)
                chunk = original[begin:end]
                if chunk.count(old) != 1:
                    raise RuntimeError('RESTORE source anchor differs: ' + label)
                (scratch / source).write_text(original[:begin] + chunk.replace(old, new) + original[end:])
                begin = proof.index('def leaveRestore (')
                end = proof.rindex('/--', begin, proof.index('theorem leaveRestore_run'))
                chunk = proof[begin:end]
                if chunk.count(old) < 1:
                    raise RuntimeError('literal RESTORE anchor differs: ' + label)
                (scratch / restore).write_text(proof[:begin] + chunk.replace(old, new) + proof[end:])
            else:
                if original.count(old) != 1:
                    raise RuntimeError('checksum source anchor differs: ' + label)
                (scratch / source).write_text(original.replace(old, new))
                (scratch / restore).write_text(proof)
            result = run(scratch)
            first = re.search(r'^error: ([^\n]+)', result.stdout, re.MULTILINE)
            hit = re.match(re.escape(str(file)) + r':(\d+):', first.group(1)) if first else None
            text = (scratch / file).read_text()
            begin = text.index('theorem ' + theorem + ' ')
            rest = text[begin:]
            next_decl = re.search(r'\n(?:theorem|/--|end)\b', rest)
            high = len(text.splitlines()) if next_decl is None else text[:begin + next_decl.start()].count('\n') + 1
            low = text[:begin].count('\n') + 1
            exhausted = any(term in result.stdout.lower() for term in (
                'maximum recursion depth', 'maximum number of heartbeats', 'deterministic timeout'))
            if result.returncode == 0 or hit is None or not low <= int(hit.group(1)) <= high or exhausted:
                raise RuntimeError(label + ' lacks a direct non-resource proof failure:\n' + result.stdout)
            print('KILLED ' + label + ': ' + first.group(1), flush=True)
        print('PASS: seven actual RESTORE/checksum mutants; no resource failures', flush=True)


if __name__ == '__main__':
    main()
