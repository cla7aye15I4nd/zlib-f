#!/usr/bin/env python3
"""Reject incorrect results from both public gz offset entries."""
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
        ('null-handle', 'def gzoffset64 (', '/-- `z_off_t ZEXPORT gzoffset(',
         'if file.isNone then return -1', 'if file.isNone then return 0'),
        ('subtract-input', 'def gzoffset64 (', '/-- `z_off_t ZEXPORT gzoffset(',
         'offset ← i64sub offset (u32ToI64 z.avail_in)',
         'offset ← i64add offset (u32ToI64 z.avail_in)'),
        ('mode-check', 'def gzoffset64 (', '/-- `z_off_t ZEXPORT gzoffset(',
         'if s.mode == GZ_READ then', 'if s.mode == GZ_WRITE then'),
        ('wrapper-result', 'def gzoffset (', '/-- `int ZEXPORT gzeof(',
         'return if ret == ret then ret else -1', 'return -1'),
    )
    with tempfile.TemporaryDirectory(prefix="gz-offset-mutants-") as name:
        scratch = Path(name)
        for file in ("lakefile.toml", "lean-toolchain"):
            shutil.copy2(root / file, scratch / file)
        shutil.copytree(root / "ZlibF", scratch / "ZlibF")
        shutil.copytree(root / ".lake", scratch / ".lake", ignore=shutil.ignore_patterns("*.tmp.*"))
        def build():
            return subprocess.run(["lake", "build", "ZlibF.Proof.«public-gz-offset»"],
                cwd=scratch, env=env, text=True, stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT, timeout=600)
        baseline = build()
        if baseline.returncode:
            raise RuntimeError("unmutated baseline failed:\n" + baseline.stdout)
        target = scratch / "ZlibF/Zlib/gzlib.c.lean"
        original = target.read_text()
        for label, start, end, old, new in cases:
            before, rest = original.split(start, 1)
            middle, after = rest.split(end, 1)
            if middle.count(old) != 1:
                raise RuntimeError("expected one mutation site for " + label)
            target.write_text(before + start + middle.replace(old, new) + end + after)
            result = build()
            error = re.search(r"^error: ([^\n]+)", result.stdout, re.MULTILINE)
            if result.returncode == 0 or error is None or not (
                error.group(1).startswith("ZlibF/Proof/public-gz-offset.lean:")
            ) or "maximum recursion depth" in error.group(1):
                raise RuntimeError(label + " survived or failed elsewhere:\n" + result.stdout)
            print("KILLED " + label + ": " + error.group(1), flush=True)
            target.write_text(original)


if __name__ == "__main__":
    main()
