#!/usr/bin/env python3
"""Synchronize CODELENS repeat cuts; reject broken counter execution."""
from pathlib import Path
import os
import re
import shutil
import subprocess
import tempfile


def main():
    root = Path(__file__).resolve().parents[2]
    source = Path("ZlibF/Zlib/inflate.c.lean")
    dynamic = Path("ZlibF/Proof/inflate.c.dynamic-install.lean")
    proof = Path("ZlibF/Proof/inflate.c.codelens-repeat.lean")
    originals = {p: (root / p).read_text() for p in (source, dynamic, proof)}
    env = os.environ.copy()
    env["LC_ALL"] = "C"

    def run(where, args):
        return subprocess.run(args, cwd=where, env=env, text=True,
                              stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=600)

    def replace_part(text, start, end, old, new):
        a = text.index(start)
        b = text.index(end, a)
        part = text[a:b]
        if part.count(old) != 1:
            raise RuntimeError("ambiguous mutation: " + old)
        return text[:a] + part.replace(old, new) + text[b:]

    with tempfile.TemporaryDirectory(prefix="inflate-codelens-repeat-") as name:
        scratch = Path(name)
        for file in ("lakefile.toml", "lean-toolchain"):
            shutil.copy2(root / file, scratch / file)
        shutil.copytree(root / "ZlibF", scratch / "ZlibF")
        shutil.copytree(root / ".lake", scratch / ".lake", ignore=shutil.ignore_patterns("*.tmp.*"))
        target = "ZlibF.Proof.«inflate.c.codelens-loop»"
        baseline = run(scratch, ["lake", "build", target])
        if baseline.returncode:
            raise RuntimeError("baseline failed:\n" + baseline.stdout)
        print("baseline: actual repeat writes and counter loop check", flush=True)
        variants = (
            ("omit-repeat-decrement", "set { l with copy := l.copy - 1 }",
             "set { l with copy := l.copy }", "def clRepeatCond", "def clRepeatBody",
             "theorem clRepeatCond_run", "theorem clRepeatBody_run"),
            ("omit-have-increment", "wrS c.st fun s => { s with «have» := s.«have» + 1 }",
             "wrS c.st fun s => { s with «have» := s.«have» }", "def clRepeatBody", "def clRepeat (",
             "theorem clRepeatBody_run", "/-- The actual post-decrement"),
        )
        for label, old, new, start, end, theorem, proof_end in variants:
            for path, text in originals.items():
                if path == proof:
                    changed = replace_part(text, start, end, old, new)
                else:
                    begin = "def inflate_CODELENS" if path == source else "def clRead ("
                    stop = "/-- `case LENLENS:" if path == source else "def clTables ("
                    if label == "omit-have-increment":
                        a = text.index(begin)
                        begin = text.index("-- while (copy--)", a)
                        # The repeat body is the last have increment in this slice.
                        b = text.index(stop, begin)
                        part = text[begin:b]
                        if part.count(old) != 1:
                            raise RuntimeError("ambiguous repeat-body mutation")
                        changed = text[:begin] + part.replace(old, new) + text[b:]
                    else:
                        changed = replace_part(text, begin, stop, old, new)
                (scratch / path).write_text(changed)
            result = run(scratch, ["lake", "build", target])
            first = re.search(r"^error: ([^\n]+)", result.stdout, re.MULTILINE)
            hit = re.match(re.escape(str(proof)) + r":(\d+):", first.group(1)) if first else None
            text = (scratch / proof).read_text()
            a = text[:text.index(theorem)].count("\n") + 1
            b = text[:text.index(proof_end)].count("\n") + 1
            exhausted = any(word in result.stdout.lower() for word in (
                "maximum recursion depth", "maximum number of heartbeats", "deterministic timeout"))
            if result.returncode == 0 or hit is None or not a <= int(hit.group(1)) < b or exhausted:
                raise RuntimeError(label + " survived or failed elsewhere:\n" + result.stdout)
            cut = (scratch / dynamic).read_text().split("def clLensPre", 1)[0]
            (scratch / "CodelensCutpoint.lean").write_text(cut + "\nend Zlib.Inflate.Proofs\n")
            checked = run(scratch, ["lake", "env", "lean", "CodelensCutpoint.lean"])
            if checked.returncode:
                raise RuntimeError("synchronized CODELENS equality failed:\n" + checked.stdout)
            print("KILLED " + label + ": " + first.group(1) + "; source equality still checks", flush=True)


if __name__ == "__main__":
    main()
