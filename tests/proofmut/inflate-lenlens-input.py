#!/usr/bin/env python3
"""Mutate the actual LENLENS prefix loop with its source cutpoint synchronized."""
from pathlib import Path
import os
import re
import shutil
import subprocess
import tempfile


def main():
    root = Path(__file__).resolve().parents[2]
    source = Path("ZlibF/Zlib/inflate.c.lean")
    proof = Path("ZlibF/Proof/inflate.c.main.table3.lean")
    originals = {p: (root / p).read_text() for p in (source, proof)}
    env = os.environ.copy()
    env["LC_ALL"] = "C"

    def run(where, args):
        return subprocess.run(args, cwd=where, env=env, text=True,
                              stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=600)

    with tempfile.TemporaryDirectory(prefix="inflate-lenlens-input-") as name:
        scratch = Path(name)
        for file in ("lakefile.toml", "lean-toolchain"):
            shutil.copy2(root / file, scratch / file)
        shutil.copytree(root / "ZlibF", scratch / "ZlibF")
        shutil.copytree(root / ".lake", scratch / ".lake", ignore=shutil.ignore_patterns("*.tmp.*"))
        target = "ZlibF.Proof.«inflate.c.construction-invariant»"
        baseline = run(scratch, ["lake", "build", target])
        if baseline.returncode:
            raise RuntimeError("baseline failed:\n" + baseline.stdout)
        print("baseline: actual LENLENS prefix loop checks", flush=True)
        variants = (
            ('short-length-read', 'NEEDBITS 3', 'NEEDBITS 2'),
            ('omit-prefix-advance', 'wrS c.st fun s => { s with «have» := s.«have» + 1 }',
             'wrS c.st fun s => { s with «have» := s.«have» }'),
        )
        for label, old, new in variants:
            for path in originals:
                text = originals[path]
                start = text.index("def inflate_LENLENS (" if path == source else "def llBody (")
                end = text.index("-- while (state->have < 19)" if path == source else "def lzCond (", start)
                part = text[start:end]
                if part.count(old) != 1:
                    raise RuntimeError("ambiguous mutation: " + label)
                (scratch / path).write_text(text[:start] + part.replace(old, new) + text[end:])
            result = run(scratch, ["lake", "build", target])
            first = re.search(r"^error: ([^\n]+)", result.stdout, re.MULTILINE)
            hit = re.match(re.escape(str(proof)) + r":(\d+):", first.group(1)) if first else None
            text = (scratch / proof).read_text()
            start = text[:text.index("theorem llBody_run")].count("\n") + 1
            end = len(text.splitlines()) + 1
            exhausted = any(word in result.stdout.lower() for word in (
                "maximum recursion depth", "maximum number of heartbeats", "deterministic timeout"))
            if result.returncode == 0 or hit is None or not start <= int(hit.group(1)) < end or exhausted:
                raise RuntimeError(label + " survived or failed elsewhere:\n" + result.stdout)
            cut = text.split("/-- One iteration of the first loop", 1)[0]
            (scratch / "LookupCutpoint.lean").write_text(cut + "\nend Zlib.Inflate.Proofs\n")
            checked = run(scratch, ["lake", "env", "lean", "LookupCutpoint.lean"])
            if checked.returncode:
                raise RuntimeError("synchronized source equality failed:\n" + checked.stdout)
            print("KILLED " + label + ": " + first.group(1) + "; source equality still checks", flush=True)


if __name__ == "__main__":
    main()
