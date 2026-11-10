#!/usr/bin/env python3
"""Keep the actual MATCH source cut equal and reject corrupted copies."""
from pathlib import Path
import os
import re
import shutil
import subprocess
import tempfile


def main():
    root = Path(__file__).resolve().parents[2]
    source = Path("ZlibF/Zlib/inflate.c.lean")
    proof = Path("ZlibF/Proof/inflate.c.match-copy.lean")
    originals = {p: (root / p).read_text() for p in (source, proof)}
    env = os.environ.copy()
    env["LC_ALL"] = "C"

    def run(where, args):
        return subprocess.run(args, cwd=where, env=env, text=True,
                              stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=600)

    def edit(text, begin, end, old, new):
        a = text.index(begin)
        b = text.index(end, a)
        part = text[a:b]
        if part.count(old) != 1:
            raise RuntimeError("ambiguous mutation: " + old)
        return text[:a] + part.replace(old, new) + text[b:]

    with tempfile.TemporaryDirectory(prefix="inflate-match-copy-") as name:
        scratch = Path(name)
        for file in ("lakefile.toml", "lean-toolchain"):
            shutil.copy2(root / file, scratch / file)
        shutil.copytree(root / "ZlibF", scratch / "ZlibF")
        shutil.copytree(root / ".lake", scratch / ".lake", ignore=shutil.ignore_patterns("*.tmp.*"))
        target = "ZlibF.Proof.«inflate.c.caller-buffers»"
        baseline = run(scratch, ["lake", "build", target])
        if baseline.returncode:
            raise RuntimeError("baseline failed:\n" + baseline.stdout)
        print("baseline: complete actual MATCH copy loop checks", flush=True)
        variants = (
            ("zero-byte-write", "byte", "store8 l.put b", "store8 l.put 0"),
            ("omit-source-increment", "byte", "let f ← l.from_.add 1", "let f ← l.from_.add 0"),
            ("omit-copy-decrement", "cond", "let n := l.copy - 1", "let n := l.copy"),
        )
        for label, stage, old, new in variants:
            src = edit(originals[source], "def inflate_MATCH (", "/-- The bit-extraction part", old, new)
            text = edit(originals[proof], "def matchCopyByte", "def matchCopyLoop", old, new)
            (scratch / source).write_text(src)
            (scratch / proof).write_text(text)
            result = run(scratch, ["lake", "build", target])
            first = re.search(r"^error: ([^\n]+)", result.stdout, re.MULTILINE)
            hit = re.match(re.escape(str(proof)) + r":(\d+):", first.group(1)) if first else None
            begin, end = ("theorem matchCopyByte_run", "theorem matchCopyCond_run") if stage == "byte" else (
                "theorem matchCopyCond_run", "theorem matchCopyWhile_run")
            a = text[:text.index(begin)].count("\n") + 1
            b = text[:text.index(end)].count("\n") + 1
            exhausted = any(word in result.stdout.lower() for word in (
                "maximum recursion depth", "maximum number of heartbeats", "deterministic timeout"))
            if result.returncode == 0 or hit is None or not a <= int(hit.group(1)) < b or exhausted:
                raise RuntimeError(label + " survived or failed elsewhere:\n" + result.stdout)
            cut = text.split("/-- One actual byte copy", 1)[0] + text[text.index("/-- Complete MATCH source"):]
            (scratch / "MatchCopyCutpoint.lean").write_text(cut)
            checked = run(scratch, ["lake", "env", "lean", "MatchCopyCutpoint.lean"])
            if checked.returncode:
                raise RuntimeError("synchronized actual source cut failed:\n" + checked.stdout)
            print("KILLED " + label + ": " + first.group(1) + "; source cut still checks", flush=True)


if __name__ == "__main__":
    main()
