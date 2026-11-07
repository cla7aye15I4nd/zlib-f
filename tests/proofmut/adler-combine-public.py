#!/usr/bin/env python3
"""Reject changes to both Adler combination entries and negative-length handling."""
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
        ("negative-length", "def adler32_combine_ (", "/-- `uLong ZEXPORT adler32_combine(",
         "if len2 < 0 then return 0xffffffff", "if len2 < 0 then return 0"),
        ("combine", "def adler32_combine (", "/-- `uLong ZEXPORT adler32_combine64(",
         "  adler32_combine_ adler1 adler2 len2", "  pure 0"),
        ("combine64", "def adler32_combine64 (", "end Zlib.Adler32",
         "  adler32_combine_ adler1 adler2 len2", "  pure 0"),
    )
    with tempfile.TemporaryDirectory(prefix="adler-combine-mutants-") as name:
        scratch = Path(name)
        for file in ("lakefile.toml", "lean-toolchain"):
            shutil.copy2(root / file, scratch / file)
        shutil.copytree(root / "ZlibF", scratch / "ZlibF")
        shutil.copytree(root / ".lake", scratch / ".lake", ignore=shutil.ignore_patterns("*.tmp.*"))
        def build():
            return subprocess.run(["lake", "build", "ZlibF.Proof.«public-adler-combine»"],
                cwd=scratch, env=env, text=True, stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT, timeout=600)
        baseline = build()
        if baseline.returncode:
            raise RuntimeError("unmutated baseline failed:\n" + baseline.stdout)
        target = scratch / "ZlibF/Zlib/adler32.c.lean"
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
                (error.group(1).startswith("ZlibF/Proof/adler32.c.lean:") and 850 <= int(error.group(1).split(":")[1]) <= 990) or
                error.group(1).startswith("ZlibF/Proof/public-adler-combine.lean:")
            ):
                raise RuntimeError(label + " survived or failed elsewhere:\n" + result.stdout)
            print("KILLED " + label + ": " + error.group(1), flush=True)
            target.write_text(original)


if __name__ == "__main__":
    main()
