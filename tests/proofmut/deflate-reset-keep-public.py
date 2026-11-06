#!/usr/bin/env python3
"""Reject altered deflateResetKeep counter, wrapper and tree operations."""
from pathlib import Path
import os
import re
import shutil
import subprocess
import tempfile


def main():
    root = Path(__file__).resolve().parents[2]
    env = os.environ.copy()
    env["LC_ALL"] = "C"
    cases = (
        ("pending", "pending := 0, pending_out := d.pending_buf", "pending := 1, pending_out := d.pending_buf"),
        ("wrapper", "wr s (fun d => { d with wrap := w })", "wr s (fun d => d)"),
        ("trees", "  _tr_init s\n", "  pure ()\n"),
        ("return-code", "return Z_OK", "return Z_STREAM_ERROR"),
    )
    with tempfile.TemporaryDirectory(prefix="deflate-reset-keep-mutants-") as name:
        scratch = Path(name)
        for file in ("lakefile.toml", "lean-toolchain"):
            shutil.copy2(root / file, scratch / file)
        shutil.copytree(root / "ZlibF", scratch / "ZlibF")
        shutil.copytree(root / ".lake", scratch / ".lake", ignore=shutil.ignore_patterns("*.tmp.*"))

        def build():
            return subprocess.run(["lake", "build", "ZlibF.Proof.«public-deflate-reset-keep»"],
                cwd=scratch, env=env, text=True, stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT, timeout=600)

        baseline = build()
        if baseline.returncode:
            raise RuntimeError("unmutated baseline failed:\n" + baseline.stdout)
        target = scratch / "ZlibF/Zlib/deflate.c.lean"
        original = target.read_text()
        before, rest = original.split("def deflateResetKeep (", 1)
        body, after = rest.split("/-- `local void lm_init(", 1)
        for label, old, new in cases:
            if body.count(old) != 1:
                raise RuntimeError("expected one mutation site for " + label)
            target.write_text(before + "def deflateResetKeep (" + body.replace(old, new)
                              + "/-- `local void lm_init(" + after)
            result = build()
            error = re.search(r"^error: ([^\n]+)", result.stdout, re.MULTILINE)
            if result.returncode == 0 or error is None or "maximum recursion depth" in error.group(1) or "timeout" in error.group(1) or not (
                (error.group(1).startswith("ZlibF/Proof/deflate.c.life.reset.lean:") and 189 <= int(error.group(1).split(":")[1]) < 201)
            ):
                raise RuntimeError(label + " survived or failed elsewhere:\n" + result.stdout)
            print("KILLED " + label + ": " + error.group(1), flush=True)
            target.write_text(original)


if __name__ == "__main__":
    main()
