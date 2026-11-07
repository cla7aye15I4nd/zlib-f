#!/usr/bin/env python3
"""Reject changes to inflateInit_ and inflateInit2_ checks."""
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
        ("wrapper-bits", "inflateInit2_ strm DEF_WBITS version stream_size",
         "inflateInit2_ strm 14 version stream_size"),
        ("version-size", "if stream_size != 112 then", "if stream_size != 111 then"),
        ("allocation-error", "if state == none then return Z_MEM_ERROR",
         "if state == none then return Z_STREAM_ERROR"),
    )
    with tempfile.TemporaryDirectory(prefix="inflate-init-mutants-") as name:
        scratch = Path(name)
        for file in ("lakefile.toml", "lean-toolchain"):
            shutil.copy2(root / file, scratch / file)
        shutil.copytree(root / "ZlibF", scratch / "ZlibF")
        shutil.copytree(root / ".lake", scratch / ".lake", ignore=shutil.ignore_patterns("*.tmp.*"))

        def build():
            return subprocess.run(["lake", "build", "ZlibF.Proof.«public-inflate-init»"],
                cwd=scratch, env=env, text=True, stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT, timeout=600)

        baseline = build()
        if baseline.returncode:
            raise RuntimeError("unmutated baseline failed:\n" + baseline.stdout)
        target = scratch / "ZlibF/Zlib/inflate.c.lean"
        original = target.read_text()
        before, rest = original.split("def inflateInit2_ (", 1)
        body, after = rest.split("/-- `int ZEXPORT inflatePrime", 1)
        for label, old, new in cases:
            if body.count(old) != 1:
                raise RuntimeError("expected one mutation site for " + label)
            target.write_text(before + "def inflateInit2_ (" + body.replace(old, new)
                              + "/-- `int ZEXPORT inflatePrime" + after)
            result = build()
            error = re.search(r"^error: ([^\n]+)", result.stdout, re.MULTILINE)
            if result.returncode == 0 or error is None or any(term in error.group(1) for term in ("maximum recursion depth", "timeout", "heartbeats")) or not (
                (error.group(1).startswith("ZlibF/Proof/inflate.c.start.lean:") and 121 <= int(error.group(1).split(":")[1]) < 260) or
                (error.group(1).startswith("ZlibF/Proof/inflate.c.hdr.lean:") and int(error.group(1).split(":")[1]) >= 125) or
                error.group(1).startswith("ZlibF/Proof/public-inflate-init.lean:")
            ):
                raise RuntimeError(label + " survived or failed elsewhere:\n" + result.stdout)
            print("KILLED " + label + ": " + error.group(1), flush=True)
            target.write_text(original)


if __name__ == "__main__":
    main()
