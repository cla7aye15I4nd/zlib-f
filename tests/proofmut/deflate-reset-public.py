#!/usr/bin/env python3
"""Reject changes to the deflateReset hash and position reset."""
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
        ("reset-dispatch", "def deflateReset (", "/-- `int ZEXPORT deflateInit2_(",
         "if ret == Z_OK then lm_init (← castDeflateState (← zrd strm (·.state)))",
         "if ret == Z_OK then pure ()"),
        ("reset-return", "def deflateReset (", "/-- `int ZEXPORT deflateInit2_(",
         "  return ret\n", "  return Z_STREAM_ERROR\n"),
    )
    with tempfile.TemporaryDirectory(prefix="deflate-reset-mutants-") as name:
        scratch = Path(name)
        for file in ("lakefile.toml", "lean-toolchain"):
            shutil.copy2(root / file, scratch / file)
        shutil.copytree(root / "ZlibF", scratch / "ZlibF")
        shutil.copytree(root / ".lake", scratch / ".lake", ignore=shutil.ignore_patterns("*.tmp.*"))

        def build():
            return subprocess.run(["lake", "build", "ZlibF.Proof.«public-deflate-reset»"],
                cwd=scratch, env=env, text=True, stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT, timeout=600)

        baseline = build()
        if baseline.returncode:
            raise RuntimeError("unmutated baseline failed:\n" + baseline.stdout)
        target = scratch / "ZlibF/Zlib/deflate.c.lean"
        original = target.read_text()
        for label, start, end, old, new in cases:
            before, rest = original.split(start, 1)
            body, after = rest.split(end, 1)
            if body.count(old) != 1:
                raise RuntimeError("expected one mutation site for " + label)
            target.write_text(before + start + body.replace(old, new) + end + after)
            result = build()
            error = re.search(r"^error: ([^\n]+)", result.stdout, re.MULTILINE)
            if result.returncode == 0 or error is None or "maximum recursion depth" in error.group(1) or "timeout" in error.group(1) or not (
                (error.group(1).startswith("ZlibF/Proof/deflate.c.life.reset.lean:") and 401 <= int(error.group(1).split(":")[1]) < 424)
            ):
                raise RuntimeError(label + " survived or failed elsewhere:\n" + result.stdout)
            print("KILLED " + label + ": " + error.group(1), flush=True)
            target.write_text(original)


if __name__ == "__main__":
    main()
