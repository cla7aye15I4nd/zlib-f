#!/usr/bin/env python3
"""Reject changes to inflateBackEnd's status and state cleanup."""
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
        ("state-free", "ZFREES strm st", "pure ()"),
        ("state-cleared", "wrZ strm fun z => { z with state := none }",
         "wrZ strm fun z => z"),
        ("return-code", "return Z_OK", "return Z_STREAM_ERROR"),
    )
    with tempfile.TemporaryDirectory(prefix="infback-end-mutants-") as name:
        scratch = Path(name)
        for file in ("lakefile.toml", "lean-toolchain"):
            shutil.copy2(root / file, scratch / file)
        shutil.copytree(root / "ZlibF", scratch / "ZlibF")
        shutil.copytree(root / ".lake", scratch / ".lake", ignore=shutil.ignore_patterns("*.tmp.*"))

        def build():
            return subprocess.run(["lake", "build", "ZlibF.Proof.«public-infback-end»"],
                cwd=scratch, env=env, text=True, stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT, timeout=600)

        baseline = build()
        if baseline.returncode:
            raise RuntimeError("unmutated baseline failed:\n" + baseline.stdout)
        target = scratch / "ZlibF/Zlib/infback.c.lean"
        original = target.read_text()
        before, rest = original.split("def inflateBackEnd (", 1)
        body, after = rest.split("end Zlib.Infback", 1)
        for label, old, new in cases:
            if body.count(old) != 1:
                raise RuntimeError("expected one mutation site for " + label)
            target.write_text(before + "def inflateBackEnd (" + body.replace(old, new)
                              + "end Zlib.Infback" + after)
            result = build()
            error = re.search(r"^error: ([^\n]+)", result.stdout, re.MULTILINE)
            if result.returncode == 0 or error is None or "maximum recursion depth" in error.group(1) or not (
                (error.group(1).startswith("ZlibF/Proof/infback.c.end.lean:") and 23 <= int(error.group(1).split(":")[1]) < 60) or
                error.group(1).startswith("ZlibF/Proof/public-infback-end.lean:")
            ):
                raise RuntimeError(label + " survived or failed elsewhere:\n" + result.stdout)
            print("KILLED " + label + ": " + error.group(1), flush=True)
            target.write_text(original)


if __name__ == "__main__":
    main()
