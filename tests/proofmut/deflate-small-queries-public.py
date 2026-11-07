#!/usr/bin/env python3
"""Reject changed results in four public deflate state queries."""
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
        ("used-field", "def deflateUsed (", "/-- `int ZEXPORT deflatePrime(",
         "if hasBits then some d.bi_used else none", "if hasBits then some d.bi_valid else none"),
        ("used-optional", "def deflateUsed (", "/-- `int ZEXPORT deflatePrime(",
         "if hasBits then some d.bi_used else none", "if hasBits then none else some d.bi_used"),
        ("tune-good", "def deflateTune (", "/-- `z_size_t ZEXPORT deflateBound_z(",
         "good_match := good_length.toUInt32", "good_match := max_lazy.toUInt32"),
        ("tune-chain", "def deflateTune (", "/-- `z_size_t ZEXPORT deflateBound_z(",
         "max_chain_length := max_chain.toUInt32", "max_chain_length := max_lazy.toUInt32"),
        ("header-wrap", "def deflateSetHeader (", "/-- `int ZEXPORT deflatePending(",
         "if (← rd s (·.wrap)) != 2 then", "if (← rd s (·.wrap)) != 1 then"),
        ("header-pointer", "def deflateSetHeader (", "/-- `int ZEXPORT deflatePending(",
         "gzhead := head", "gzhead := none"),
        ("pending-overflow", "def deflatePending (", "/-- `int ZEXPORT deflateUsed(",
         "if p.toUInt64 != d.pending then", "if p.toUInt64 == d.pending then"),
        ("pending-bits", "def deflatePending (", "/-- `int ZEXPORT deflateUsed(",
         "let bits := if hasBits then some d.bi_valid else none",
         "let bits := if hasBits then some d.bi_used else none"),
    )
    with tempfile.TemporaryDirectory(prefix="deflate-queries-mutants-") as name:
        scratch = Path(name)
        for file in ("lakefile.toml", "lean-toolchain"):
            shutil.copy2(root / file, scratch / file)
        shutil.copytree(root / "ZlibF", scratch / "ZlibF")
        shutil.copytree(root / ".lake", scratch / ".lake", ignore=shutil.ignore_patterns("*.tmp.*"))

        def build():
            return subprocess.run(["lake", "build", "ZlibF.Proof.«public-deflate-small-queries»"],
                cwd=scratch, env=env, text=True, stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT, timeout=600)

        baseline = build()
        if baseline.returncode:
            raise RuntimeError("unmutated baseline failed:\n" + baseline.stdout)
        target = scratch / "ZlibF/Zlib/deflate.c.lean"
        original = target.read_text()
        for label, start, end, old, new in cases:
            before, rest = original.split(start, 1)
            middle, after = rest.split(end, 1)
            if middle.count(old) != 1:
                raise RuntimeError("expected one mutation site for " + label)
            target.write_text(before + start + middle.replace(old, new) + end + after)
            result = build()
            error = re.search(r"^error: ([^\n]+)", result.stdout, re.MULTILINE)
            if result.returncode == 0 or error is None or "maximum recursion depth" in error.group(1) or not (
                error.group(1).startswith("ZlibF/Proof/public-deflate-small-queries.lean:")
            ):
                raise RuntimeError(label + " survived or failed elsewhere:\n" + result.stdout)
            print("KILLED " + label + ": " + error.group(1), flush=True)
            target.write_text(original)


if __name__ == "__main__":
    main()
