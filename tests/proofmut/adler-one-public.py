#!/usr/bin/env python3
"""Reject changes to the one-byte Adler entry's conditional reductions."""
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
        ("low-reduction", "if adler >= BASE then adler := adler - BASE",
         "if adler > BASE then adler := adler - BASE"),
        ("high-reduction", "if sum2 >= BASE then sum2 := sum2 - BASE",
         "if sum2 > BASE then sum2 := sum2 - BASE"),
    )
    with tempfile.TemporaryDirectory(prefix="adler-one-mutants-") as name:
        scratch = Path(name)
        for file in ("lakefile.toml", "lean-toolchain"):
            shutil.copy2(root / file, scratch / file)
        shutil.copytree(root / "ZlibF", scratch / "ZlibF")
        shutil.copytree(root / ".lake", scratch / ".lake", ignore=shutil.ignore_patterns("*.tmp.*"))

        def build():
            return subprocess.run(["lake", "build", "ZlibF.Proof.«public-adler-update»"],
                cwd=scratch, env=env, text=True, stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT, timeout=600)

        baseline = build()
        if baseline.returncode:
            raise RuntimeError("unmutated baseline failed:\n" + baseline.stdout)
        target = scratch / "ZlibF/Zlib/adler32.c.lean"
        original = target.read_text()
        before, rest = original.split("def adler32_z (", 1)
        branch, after = rest.split("  -- if (len < 16)", 1)
        for label, old, new in cases:
            if branch.count(old) != 1:
                raise RuntimeError("expected one mutation site for " + label)
            target.write_text(before + "def adler32_z (" + branch.replace(old, new)
                              + "  -- if (len < 16)" + after)
            result = build()
            error = re.search(r"^error: ([^\n]+)", result.stdout, re.MULTILINE)
            if result.returncode == 0 or error is None or "maximum recursion depth" in error.group(1) or not (
                error.group(1).startswith("ZlibF/Proof/adler32.c.lean:") or
                error.group(1).startswith("ZlibF/Proof/adler32.c.public-one.lean:")
            ):
                raise RuntimeError(label + " survived or failed elsewhere:\n" + result.stdout)
            print("KILLED " + label + ": " + error.group(1), flush=True)
            target.write_text(original)


if __name__ == "__main__":
    main()
