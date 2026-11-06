#!/usr/bin/env python3
"""Reject changes to inflateSetDictionary rejection checks."""
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
        ("null-source", "if (← inflateStateCheck strm) != 0 || dictionary == .null then return Z_STREAM_ERROR",
         "if (← inflateStateCheck strm) != 0 then return Z_STREAM_ERROR"),
        ("wrong-state", "if s.wrap != 0 && s.mode != DICT then return Z_STREAM_ERROR",
         "if s.wrap != 0 && s.mode == DICT then return Z_STREAM_ERROR"),
        ("wrong-checksum", "if dictid != s.check then return Z_DATA_ERROR",
         "if dictid != s.check then return Z_OK"),
        ("missing-memory-mode", "setMode st MEM\n    return Z_MEM_ERROR",
         "setMode st DICT\n    return Z_MEM_ERROR"),
        ("wrong-allocation-error", "setMode st MEM\n    return Z_MEM_ERROR",
         "setMode st MEM\n    return Z_STREAM_ERROR"),
        ("missing-dictionary-flag", "wrS st fun s => { s with havedict := 1 }",
         "wrS st fun s => { s with havedict := 0 }"),
        ("wrong-success-mode", "wrS st fun s => { s with havedict := 1 }",
         "wrS st fun s => { s with havedict := 1, mode := MEM }"),
    )
    with tempfile.TemporaryDirectory(prefix="inflate-setdict-mutants-") as name:
        scratch = Path(name)
        for file in ("lakefile.toml", "lean-toolchain"):
            shutil.copy2(root / file, scratch / file)
        shutil.copytree(root / "ZlibF", scratch / "ZlibF")
        shutil.copytree(root / ".lake", scratch / ".lake")

        def build():
            return subprocess.run(["lake", "build", "ZlibF.Proof.«public-inflate-setdict»"],
                cwd=scratch, env=env, text=True, stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT, timeout=600)

        baseline = build()
        if baseline.returncode:
            raise RuntimeError("unmutated baseline failed:\n" + baseline.stdout)
        target = scratch / "ZlibF/Zlib/inflate.c.lean"
        original = target.read_text()
        before, rest = original.split("def inflateSetDictionary (", 1)
        body, after = rest.split("/-- `int ZEXPORT inflateGetHeader", 1)
        for label, old, new in cases:
            if body.count(old) != 1:
                raise RuntimeError("expected one mutation site for " + label)
            target.write_text(before + "def inflateSetDictionary (" + body.replace(old, new)
                              + "/-- `int ZEXPORT inflateGetHeader" + after)
            result = build()
            error = re.search(r"^error: ([^\n]+)", result.stdout, re.MULTILINE)
            if result.returncode == 0 or error is None or any(term in error.group(1) for term in ("maximum recursion depth", "timeout", "heartbeats")) or not (
                error.group(1).startswith("ZlibF/Proof/inflate.c.dict.lean:") or
                error.group(1).startswith("ZlibF/Proof/inflate.c.public-setdict.lean:") or
                error.group(1).startswith("ZlibF/Proof/inflate.c.public-setdict-safe.lean:") or
                error.group(1).startswith("ZlibF/Proof/inflate.c.public-setdict-content.lean:") or
                error.group(1).startswith("ZlibF/Proof/inflate.c.public-setdict-mode.lean:") or
                error.group(1).startswith("ZlibF/Proof/inflate.c.public-setdict-success.lean:") or
                error.group(1).startswith("ZlibF/Proof/public-inflate-setdict.lean:")
            ):
                raise RuntimeError(label + " survived or failed elsewhere:\n" + result.stdout)
            print("KILLED " + label + ": " + error.group(1), flush=True)
            target.write_text(original)


if __name__ == "__main__":
    main()
