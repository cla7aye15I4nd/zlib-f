#!/usr/bin/env python3
"""Synchronize actual slow lookup source cuts; reject execution mistakes."""
from pathlib import Path
import os
import re
import shutil
import subprocess
import tempfile


def main():
    root = Path(__file__).resolve().parents[2]
    source = Path("ZlibF/Zlib/inflate.c.lean")
    data = Path("ZlibF/Proof/inflate.c.lookup-data.lean")
    sub = Path("ZlibF/Proof/inflate.c.lookup-subtable.lean")
    originals = {p: (root / p).read_text() for p in (source, data, sub)}
    env = os.environ.copy()
    env["LC_ALL"] = "C"

    def run(where, args):
        return subprocess.run(args, cwd=where, env=env, text=True,
                              stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=600)

    def replace_cut(text, begin, end, old, new):
        a = text.index(begin)
        b = text.index(end, a)
        part = text[a:b]
        if part.count(old) != 1:
            raise RuntimeError("ambiguous source mutation: " + old)
        return text[:a] + part.replace(old, new) + text[b:]

    with tempfile.TemporaryDirectory(prefix="inflate-slow-lookup-") as name:
        scratch = Path(name)
        for file in ("lakefile.toml", "lean-toolchain"):
            shutil.copy2(root / file, scratch / file)
        shutil.copytree(root / "ZlibF", scratch / "ZlibF")
        shutil.copytree(root / ".lake", scratch / ".lake", ignore=shutil.ignore_patterns("*.tmp.*"))
        target = "ZlibF.Proof.«inflate.c.slow-length»"
        baseline = run(scratch, ["lake", "build", target])
        if baseline.returncode:
            raise RuntimeError("baseline failed:\n" + baseline.stdout)
        print("baseline: actual slow length lookup boundary checks", flush=True)
        variants = (
            ("root-reject-exact-bits", data, "def lookup1 (", "def lookup2 (",
             "def dataLookupBody (", "theorem lookup1_data_eq", "theorem dataLookupBody_run",
             "/-- The actual LEN/DIST root lookup", "/-- One actual root-table read",
             "here.bits.toUInt32 <= (← get).bits", "here.bits.toUInt32 < (← get).bits"),
            ("root-omit-refill", data, "def lookup1 (", "def lookup2 (",
             "def dataLookupBody (", "theorem lookup1_data_eq", "theorem dataLookupBody_run",
             "/-- The actual LEN/DIST root lookup", "/-- One actual root-table read",
             "PULLBYTE\n", "pure ()\n"),
            ("sub-omit-root-width", sub, "def lookup2 (", "/-- `case DIST:`",
             "def dataSubLookupBody (", "theorem lookup2_data_eq", "theorem dataSubLookupBody_run",
             "/-- The complete actual second-level lookup", "/-- The actual second-level mask",
             "last.bits.toUInt32 + here.bits.toUInt32", "here.bits.toUInt32"),
            ("sub-wrong-shift", sub, "def lookup2 (", "/-- `case DIST:`",
             "def dataSubLookupBody (", "theorem lookup2_data_eq", "theorem dataSubLookupBody_run",
             "/-- The complete actual second-level lookup", "/-- The actual second-level mask",
             "shr32 b last.bits.toUInt32", "shr32 b last.op.toUInt32"),
        )
        for label, proof, src_begin, src_end, cut_begin, cut_end, theorem, proof_end, cut_stop, old, new in variants:
            for path, text in originals.items():
                (scratch / path).write_text(text)
            (scratch / source).write_text(replace_cut(originals[source], src_begin, src_end, old, new))
            changed = replace_cut(originals[proof], cut_begin, cut_end, old, new)
            (scratch / proof).write_text(changed)
            result = run(scratch, ["lake", "build", target])
            first = re.search(r"^error: ([^\n]+)", result.stdout, re.MULTILINE)
            hit = re.match(re.escape(str(proof)) + r":(\d+):", first.group(1)) if first else None
            a = changed[:changed.index(theorem)].count("\n") + 1
            b = changed[:changed.index(proof_end)].count("\n") + 1
            exhausted = any(word in result.stdout.lower() for word in (
                "maximum recursion depth", "maximum number of heartbeats", "deterministic timeout"))
            if result.returncode == 0 or hit is None or not a <= int(hit.group(1)) < b or exhausted:
                raise RuntimeError(label + " survived or failed elsewhere:\n" + result.stdout)
            cut = changed.split(cut_stop, 1)[0]
            (scratch / "SlowLookupCutpoint.lean").write_text(cut + "\nend Zlib.Inflate.Proofs\n")
            checked = run(scratch, ["lake", "env", "lean", "SlowLookupCutpoint.lean"])
            if checked.returncode:
                raise RuntimeError("synchronized source equality failed:\n" + checked.stdout)
            print("KILLED " + label + ": " + first.group(1) + "; source equality still checks", flush=True)


if __name__ == "__main__":
    main()
