#!/usr/bin/env python3
"""Reject changes to Adler short-loop and long-block updates."""
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
        ("byte-advance", "let buf ← s.buf.add 1", "let buf ← s.buf.add 2"),
        ("block-byte", "let b ← index8 s.buf i", "let b ← index8 s.buf (i + 1)"),
        ("wrapper-length", "adler32_z adler buf len.toUInt64",
         "adler32_z adler buf (len.toUInt64 + 1)"),
    )
    with tempfile.TemporaryDirectory(prefix="adler-block-mutants-") as name:
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
        for label, old, new in cases:
            if original.count(old) < 1:
                raise RuntimeError("missing mutation site for " + label)
            target.write_text(original.replace(old, new, 1))
            result = build()
            error = re.search(r"^error: ([^\n]+)", result.stdout, re.MULTILINE)
            if result.returncode == 0 or error is None or ("maximum recursion depth" in error.group(1) or "timeout" in error.group(1) or "heartbeats" in error.group(1)) or not (
                error.group(1).startswith("ZlibF/Proof/adler32.c.lean:") or
                error.group(1).startswith("ZlibF/Proof/adler32.c.public-one.lean:") or
                error.group(1).startswith("ZlibF/Proof/adler32.c.public-any.lean:") or
                error.group(1).startswith("ZlibF/Proof/public-adler-update.lean:")
            ):
                raise RuntimeError(label + " survived or failed elsewhere:\n" + result.stdout)
            print("KILLED " + label + ": " + error.group(1), flush=True)
            target.write_text(original)


if __name__ == "__main__":
    main()
