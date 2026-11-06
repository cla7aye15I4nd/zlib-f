#!/usr/bin/env python3
"""Reject changed results in the public inflate prime query."""
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
        ("negative-clear", "def inflatePrime (", "/-- `local int updatewindow(",
         "wrS state fun s => { s with hold := 0, bits := 0 }",
         "wrS state fun s => { s with hold := 1, bits := 0 }"),
        ("count-limit", "def inflatePrime (", "/-- `local int updatewindow(",
         "if bits > 16 || s.bits + i2u bits > 32 then", "if bits > 15 || s.bits + i2u bits > 32 then"),
        ("buffer-limit", "def inflatePrime (", "/-- `local int updatewindow(",
         "if bits > 16 || s.bits + i2u bits > 32 then", "if bits > 16 || s.bits + i2u bits > 31 then"),
        ("inserted-bits", "def inflatePrime (", "/-- `local int updatewindow(",
         "bits := s.bits + i2u bits", "bits := s.bits - i2u bits"),
    )
    with tempfile.TemporaryDirectory(prefix="inflate-queries-mutants-") as name:
        scratch = Path(name)
        for file in ("lakefile.toml", "lean-toolchain"):
            shutil.copy2(root / file, scratch / file)
        shutil.copytree(root / "ZlibF", scratch / "ZlibF")
        shutil.copytree(root / ".lake", scratch / ".lake", ignore=shutil.ignore_patterns("*.tmp.*"))

        def build():
            return subprocess.run(["lake", "build", "ZlibF.Proof.«public-inflate-prime»"],
                cwd=scratch, env=env, text=True, stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT, timeout=600)

        baseline = build()
        if baseline.returncode:
            raise RuntimeError("unmutated baseline failed:\n" + baseline.stdout)
        target = scratch / "ZlibF/Zlib/inflate.c.lean"
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
                error.group(1).startswith("ZlibF/Proof/public-inflate-prime.lean:")
            ):
                raise RuntimeError(label + " survived or failed elsewhere:\n" + result.stdout)
            print("KILLED " + label + ": " + error.group(1), flush=True)
            target.write_text(original)


if __name__ == "__main__":
    main()
