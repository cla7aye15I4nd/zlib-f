#!/usr/bin/env python3
"""Reject wrong dictionary length, source range, copy and output length."""
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
        ("length-clamp", "if len > d.w_size then len := d.w_size", "if len > d.w_size then len := 0"),
        ("source-offset", "psub from_ len.toNat", "psub from_ (len.toNat + 1)"),
        ("copy", "memcpyB dictionary (← psub from_ len.toNat) len.toNat", "pure ()"),
        ("reported-length", "return (Z_OK, if hasDictLength then some len else none)",
         "return (Z_OK, if hasDictLength then some 0 else none)"),
    )
    with tempfile.TemporaryDirectory(prefix="deflate-getdict-mutants-") as name:
        scratch = Path(name)
        for file in ("lakefile.toml", "lean-toolchain"):
            shutil.copy2(root / file, scratch / file)
        shutil.copytree(root / "ZlibF", scratch / "ZlibF")
        shutil.copytree(root / ".lake", scratch / ".lake", ignore=shutil.ignore_patterns("*.tmp.*"))

        def build():
            return subprocess.run(["lake", "build", "ZlibF.Proof.«public-deflate-getdict»"],
                cwd=scratch, env=env, text=True, stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT, timeout=600)

        baseline = build()
        if baseline.returncode:
            raise RuntimeError("unmutated baseline failed:\n" + baseline.stdout)
        target = scratch / "ZlibF/Zlib/deflate.c.lean"
        original = target.read_text()
        before, rest = original.split("def deflateGetDictionary (", 1)
        body, after = rest.split("/-- `int ZEXPORT deflateSetHeader(", 1)
        for label, old, new in cases:
            if body.count(old) != 1:
                raise RuntimeError("expected one mutation site for " + label)
            target.write_text(before + "def deflateGetDictionary (" + body.replace(old, new)
                              + "/-- `int ZEXPORT deflateSetHeader(" + after)
            result = build()
            error = re.search(r"^error: ([^\n]+)", result.stdout, re.MULTILINE)
            if result.returncode == 0 or error is None or "maximum recursion depth" in error.group(1) or "timeout" in error.group(1) or not (
                (error.group(1).startswith("ZlibF/Proof/deflate.c.life.getdict.lean:") and 46 <= int(error.group(1).split(":")[1]) < 115) or
                error.group(1).startswith("ZlibF/Proof/deflate.c.public-getdict.lean:") or
                error.group(1).startswith("ZlibF/Proof/public-deflate-getdict.lean:")
            ):
                raise RuntimeError(label + " survived or failed elsewhere:\n" + result.stdout)
            print("KILLED " + label + ": " + error.group(1), flush=True)
            target.write_text(original)


if __name__ == "__main__":
    main()
