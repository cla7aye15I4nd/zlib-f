#!/usr/bin/env python3
"""Reject omitted deflateEnd releases and incorrect completion status."""
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
        ("free-pending", "if pb != .null then ZFREE_bytes strm pb",
         "if pb != .null then pure ()"),
        ("free-head", "if hd != .null then ZFREE_words strm hd",
         "if hd != .null then pure ()"),
        ("free-prev", "if pv != .null then ZFREE_words strm pv",
         "if pv != .null then pure ()"),
        ("free-window", "if wd != .null then ZFREE_bytes strm wd",
         "if wd != .null then pure ()"),
        ("clear-state", "zwr strm (fun z => { z with state := none })", "zwr strm (fun z => z)"),
        ("free-state", "freeDeflateState sp", "pure ()"),
        ("busy-status", "return if status == BUSY_STATE then Z_DATA_ERROR else Z_OK",
         "return Z_OK"),
    )
    with tempfile.TemporaryDirectory(prefix="deflate-end-mutants-") as name:
        scratch = Path(name)
        for file in ("lakefile.toml", "lean-toolchain"):
            shutil.copy2(root / file, scratch / file)
        shutil.copytree(root / "ZlibF", scratch / "ZlibF")
        shutil.copytree(root / ".lake", scratch / ".lake", ignore=shutil.ignore_patterns("*.tmp.*"))

        def build():
            return subprocess.run(["lake", "build", "ZlibF.Proof.«public-deflate-end»"],
                cwd=scratch, env=env, text=True, stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT, timeout=600)

        baseline = build()
        if baseline.returncode:
            raise RuntimeError("unmutated baseline failed:\n" + baseline.stdout)
        target = scratch / "ZlibF/Zlib/deflate.c.lean"
        original = target.read_text()
        before, rest = original.split("def deflateEnd (", 1)
        body, after = rest.split("/-- `int ZEXPORT deflateResetKeep(", 1)
        for label, old, new in cases:
            if body.count(old) != 1:
                raise RuntimeError("expected one mutation site for " + label)
            target.write_text(before + "def deflateEnd (" + body.replace(old, new)
                              + "/-- `int ZEXPORT deflateResetKeep(" + after)
            result = build()
            error = re.search(r"^error: ([^\n]+)", result.stdout, re.MULTILINE)
            if result.returncode == 0 or error is None or "maximum recursion depth" in error.group(1) or not (
                (error.group(1).startswith("ZlibF/Proof/deflate.c.life.end.lean:") and 106 <= int(error.group(1).split(":")[1]) < 141)
            ):
                raise RuntimeError(label + " survived or failed elsewhere:\n" + result.stdout)
            print("KILLED " + label + ": " + error.group(1), flush=True)
            target.write_text(original)


if __name__ == "__main__":
    main()
