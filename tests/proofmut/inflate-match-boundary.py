#!/usr/bin/env python3
"""Synchronize MATCH source cuts and reject wrong selection/accounting."""
from pathlib import Path
import os
import re
import shutil
import subprocess
import tempfile


def main():
    root = Path(__file__).resolve().parents[2]
    source = Path("ZlibF/Zlib/inflate.c.lean")
    loop = Path("ZlibF/Proof/inflate.c.match-copy.lean")
    emit = Path("ZlibF/Proof/inflate.c.match-emit.lean")
    select = Path("ZlibF/Proof/inflate.c.match-source.lean")
    originals = {p: (root / p).read_text() for p in (source, loop, emit, select)}
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

    with tempfile.TemporaryDirectory(prefix="inflate-match-boundary-") as name:
        scratch = Path(name)
        for file in ("lakefile.toml", "lean-toolchain"):
            shutil.copy2(root / file, scratch / file)
        shutil.copytree(root / "ZlibF", scratch / "ZlibF")
        shutil.copytree(root / ".lake", scratch / ".lake", ignore=shutil.ignore_patterns("*.tmp.*"))
        target = "ZlibF.Proof.«inflate.c.pending-dispatch»"
        baseline = run(scratch, ["lake", "build", target])
        if baseline.returncode:
            raise RuntimeError("baseline failed:\n" + baseline.stdout)
        print("baseline: complete actual MATCH boundary checks", flush=True)
        variants = (
            ("wrong-output-source", "select", "l.put.add (-(s.offset.toNat : Int))", "l.put.add (s.offset.toNat : Int)",
             "theorem matchSelect_output_cut", "theorem matchSelect_window_cut"),
            ("omit-history-check", "select", "if copy > s.whave then", "if false then",
             "theorem matchSelect_bad_run", "theorem matchSelect_wait"),
            ("wrong-ring-origin", "select", "s.window.add ((s.wsize - copy).toNat : Int)", "s.window.add (copy.toNat : Int)",
             "theorem matchSelect_wrap_cut", "theorem matchSelect_bad_run"),
            ("omit-output-accounting", "emit", "left := l.left - copy", "left := l.left",
             "theorem matchEmit_run", "end Zlib.Inflate.Proofs"),
            ("omit-length-accounting", "emit", "length := s.length - copy", "length := s.length",
             "theorem matchEmit_run", "end Zlib.Inflate.Proofs"),
        )
        for label, stage, old, new, begin, end in variants:
            texts = dict(originals)
            texts[source] = edit(texts[source], "def inflate_MATCH (", "/-- The bit-extraction part", old, new)
            texts[loop] = edit(texts[loop], "def matchCase (", "theorem inflate_MATCH_copy_cut", old, new)
            if stage == "select":
                texts[select] = edit(texts[select], "def matchSelect (", "theorem inflate_MATCH_select_cut", old, new)
                proof = select
            else:
                texts[emit] = edit(texts[emit], "def matchEmitFrom (", "def matchEmit (", old, new)
                proof = emit
            for path, text in texts.items():
                (scratch / path).write_text(text)
            result = run(scratch, ["lake", "build", target])
            first = re.search(r"^error: ([^\n]+)", result.stdout, re.MULTILINE)
            hit = re.match(re.escape(str(proof)) + r":(\d+):", first.group(1)) if first else None
            text = texts[proof]
            a = text[:text.index(begin)].count("\n") + 1
            b = text[:text.index(end)].count("\n") + 1
            exhausted = any(word in result.stdout.lower() for word in (
                "maximum recursion depth", "maximum number of heartbeats", "deterministic timeout"))
            if result.returncode == 0 or hit is None or not a <= int(hit.group(1)) < b or exhausted:
                raise RuntimeError(label + " survived or failed elsewhere:\n" + result.stdout)
            definitions = texts[emit].split("/-- Execute the actual bounded segment", 1)[0]
            selection = texts[select][texts[select].index("/-- Actual MATCH source selection"):]
            selection = selection[:selection.index("/-- Source selection for a back-reference")]
            (scratch / "MatchBoundaryCutpoint.lean").write_text(definitions + selection + "\nend Zlib.Inflate.Proofs\n")
            checked = run(scratch, ["lake", "env", "lean", "MatchBoundaryCutpoint.lean"])
            if checked.returncode:
                raise RuntimeError("synchronized actual source cuts failed:\n" + checked.stdout)
            print("KILLED " + label + ": " + first.group(1) + "; source cut still checks", flush=True)


if __name__ == "__main__":
    main()
