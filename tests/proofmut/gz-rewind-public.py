#!/usr/bin/env python3
"""Reject altered gzrewind refusal, seek and reset behavior."""
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
        ("mode-check", "s.mode != GZ_READ || (s.err != Z_OK && s.err != Z_BUF_ERROR)",
         "s.mode != GZ_WRITE || (s.err != Z_OK && s.err != Z_BUF_ERROR)"),
        ("seek-origin", "fsLseek s.fd s.start SEEK_SET", "fsLseek s.fd s.start SEEK_CUR"),
        ("reset", "  gz_reset state\n", "  pure ()\n"),
    )
    with tempfile.TemporaryDirectory(prefix="gz-rewind-mutants-") as name:
        scratch = Path(name)
        for file in ("lakefile.toml", "lean-toolchain"):
            shutil.copy2(root / file, scratch / file)
        shutil.copytree(root / "ZlibF", scratch / "ZlibF")
        shutil.copytree(root / ".lake", scratch / ".lake", ignore=shutil.ignore_patterns("*.tmp.*"))

        def build():
            return subprocess.run(["lake", "build", "ZlibF.Proof.«public-gz-rewind»"],
                cwd=scratch, env=env, text=True, stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT, timeout=600)

        baseline = build()
        if baseline.returncode:
            raise RuntimeError("unmutated baseline failed:\n" + baseline.stdout)
        target = scratch / "ZlibF/Zlib/gzlib.c.lean"
        original = target.read_text()
        before, rest = original.split("def gzrewind (", 1)
        body, after = rest.split("/-- `z_off64_t ZEXPORT gzseek64(", 1)
        for label, old, new in cases:
            if body.count(old) != 1:
                raise RuntimeError("expected one mutation site for " + label)
            target.write_text(before + "def gzrewind (" + body.replace(old, new)
                              + "/-- `z_off64_t ZEXPORT gzseek64(" + after)
            result = build()
            error = re.search(r"^error: ([^\n]+)", result.stdout, re.MULTILINE)
            if result.returncode == 0 or error is None or "maximum recursion depth" in error.group(1) or "timeout" in error.group(1) or not (
                error.group(1).startswith("ZlibF/Proof/public-gz-rewind.lean:")
            ):
                raise RuntimeError(label + " survived or failed elsewhere:\n" + result.stdout)
            print("KILLED " + label + ": " + error.group(1), flush=True)
            target.write_text(original)


if __name__ == "__main__":
    main()
