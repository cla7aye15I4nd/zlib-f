#!/usr/bin/env python3
"""Check that gzerror's public proof rejects incorrect writes and messages."""
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
        ("wrong-error-code", "gzlib.c.lean", "def gzerror (", "/-- `void ZEXPORT gzclearerr",
         "store32 errnum s.err", "store32 errnum (s.err + 1)"),
        ("missing-error-code", "gzlib.c.lean", "def gzerror (", "/-- `void ZEXPORT gzclearerr",
         "if errnum != .null then store32 errnum s.err", "pure ()"),
        ("wrong-memory-error-text", "gzlib.c.lean", "def gzerror (", "/-- `void ZEXPORT gzclearerr",
         'if s.err == Z_MEM_ERROR then strLit "out of memory"',
         'if s.err == Z_MEM_ERROR then strLit ""'),
        ("wrong-message-pointer", "gzlib.c.lean", "def gzerror (", "/-- `void ZEXPORT gzclearerr",
         "else pure s.msg", "else pure .null"),
    )
    with tempfile.TemporaryDirectory(prefix="gzerror-public-mutants-") as name:
        scratch = Path(name)
        for file in ("lakefile.toml", "lean-toolchain"):
            shutil.copy2(root / file, scratch / file)
        shutil.copytree(root / "ZlibF", scratch / "ZlibF")
        shutil.copytree(root / ".lake", scratch / ".lake", ignore=shutil.ignore_patterns("*.tmp.*"))
        def build():
            return subprocess.run(["lake", "build", "ZlibF.Proof.«public-gz-error»"],
                cwd=scratch, env=env, text=True, stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT, timeout=600)
        baseline = build()
        if baseline.returncode:
            raise RuntimeError("unmutated baseline failed:\n" + baseline.stdout)
        for label, filename, start, end, old, new in cases:
            target = scratch / "ZlibF/Zlib" / filename
            original = target.read_text()
            before, rest = original.split(start, 1)
            body, after = rest.split(end, 1)
            if body.count(old) != 1:
                raise RuntimeError("expected one mutation site for " + label)
            target.write_text(before + start + body.replace(old, new, 1) + end + after)
            result = build()
            error = re.search(r"^error: ([^\n]+)", result.stdout, re.MULTILINE)
            expected = ("ZlibF/Proof/public-gz-error.lean:",)
            if result.returncode == 0 or error is None or not error.group(1).startswith(expected) \
                or "maximum recursion depth" in error.group(1):
                raise RuntimeError(label + " survived or failed elsewhere:\n" + result.stdout)
            print("KILLED " + label + ": " + error.group(1), flush=True)
            target.write_text(original)


if __name__ == "__main__":
    main()
