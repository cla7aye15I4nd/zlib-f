#!/usr/bin/env python3
"""Reject wrong actual data-mode dispatch without accepting resource failures."""
from pathlib import Path
import os
import re
import shutil
import subprocess
import tempfile


def main():
    root = Path(__file__).resolve().parents[2]
    source = Path("ZlibF/Zlib/inflate.c.lean")
    original = (root / source).read_text()
    rows = [line.split("\t") for line in
            (root / "tests/proofmut/inflate-data-dispatch.tsv").read_text().splitlines()
            if line and not line.startswith("#")]
    expected = {
        "dispatch-length-to-distance": ("inflate.c.data-dispatch", "LEN"),
        "dispatch-literal-to-match": ("inflate.c.data-dispatch", "LIT"),
        "dispatch-match-to-literal": ("inflate.c.data-dispatch", "MATCH"),
        "dispatch-start-wrong-mode": ("inflate.c.pending-dispatch", "LEN_start"),
        "dispatch-length-extra-wrong-mode": ("inflate.c.pending-dispatch", "LENEXT"),
        "dispatch-distance-wrong-mode": ("inflate.c.pending-dispatch", "DIST"),
        "dispatch-distance-extra-wrong-mode": ("inflate.c.pending-dispatch", "DISTEXT"),
    }
    if {row[0] for row in rows} != set(expected):
        raise RuntimeError("dispatch mutation inventory differs")
    env = os.environ.copy()
    env["LC_ALL"] = "C"
    target = "ZlibF.Proof.«inflate.c.construction-default»"

    def run(where):
        return subprocess.run(["lake", "build", target], cwd=where, env=env, text=True,
                              stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=600)

    with tempfile.TemporaryDirectory(prefix="inflate-pending-dispatch-") as directory:
        scratch = Path(directory)
        for name in ("lakefile.toml", "lean-toolchain"):
            shutil.copy2(root / name, scratch / name)
        shutil.copytree(root / "ZlibF", scratch / "ZlibF")
        shutil.copytree(root / ".lake", scratch / ".lake", ignore=shutil.ignore_patterns("*.tmp.*", "Index.*"))
        baseline = run(scratch)
        if baseline.returncode:
            raise RuntimeError("unmutated baseline failed:\n" + baseline.stdout)
        print("baseline: seven-mode scalar and buffer dispatcher checks", flush=True)
        for label, file, old, new, _ in rows:
            start = original.index("def inflate_dispatch (")
            stop = original.index("def inflate_run (", start)
            if file != str(source) or original.count(old) != 1 or old not in original[start:stop]:
                raise RuntimeError("mutation is not a unique actual dispatch branch: " + label)
            (scratch / source).write_text(original.replace(old, new))
            result = run(scratch)
            first = re.search(r"^error: ([^\n]+)", result.stdout, re.MULTILINE)
            module, name = expected[label]
            proof = Path("ZlibF/Proof") / (module + ".lean")
            hit = re.match(re.escape(str(proof)) + r":(\d+):", first.group(1)) if first else None
            text = (scratch / proof).read_text()
            begin = text.index("theorem inflate_dispatch_" + name + " ")
            remaining = text[begin:]
            next_decl = re.search(r"\n(?:theorem|end)\b", remaining)
            if next_decl is None:
                raise RuntimeError("missing next declaration: " + label)
            low = text[:begin].count("\n") + 1
            high = low + remaining[:next_decl.start()].count("\n")
            exhausted = any(term in result.stdout.lower() for term in (
                "maximum recursion depth", "maximum number of heartbeats", "deterministic timeout"))
            if result.returncode == 0 or hit is None or not low <= int(hit.group(1)) <= high or exhausted:
                raise RuntimeError(label + " survived or lacks a direct non-resource proof failure:\n" + result.stdout)
            print("KILLED " + label + ": " + first.group(1), flush=True)
        print("PASS: seven actual dispatch mutants; no resource failures", flush=True)


if __name__ == "__main__":
    main()
