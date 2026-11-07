#!/usr/bin/env python3
"""Reject mutations to each public CRC combination entry."""
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
        ("gen64", "def crc32_combine_gen64 (", "/-- `uLong ZEXPORT crc32_combine_gen(",
         "if len2 < 0 then return 0", "if len2 < 0 then return 1"),
        ("gen", "def crc32_combine_gen (", "/-- `uLong ZEXPORT crc32_combine_op(",
         "  crc32_combine_gen64 len2", "  crc32_combine_gen64 (len2 + 1)"),
        ("op", "def crc32_combine_op (", "/-- `uLong ZEXPORT crc32_combine64(",
         "pure (m ^^^ (crc2 &&& 0xffffffff))", "pure m"),
        ("combine64", "def crc32_combine64 (", "/-- `uLong ZEXPORT crc32_combine(",
         "  crc32_combine_op crc1 crc2", "  crc32_combine_op crc2 crc1"),
        ("combine", "def crc32_combine (", "end Zlib.Crc32",
         "  crc32_combine64 crc1 crc2 len2", "  crc32_combine64 crc2 crc1 len2"),
    )
    with tempfile.TemporaryDirectory(prefix="crc-combine-mutants-") as name:
        scratch = Path(name)
        for file in ("lakefile.toml", "lean-toolchain"):
            shutil.copy2(root / file, scratch / file)
        shutil.copytree(root / "ZlibF", scratch / "ZlibF")
        shutil.copytree(root / ".lake", scratch / ".lake", ignore=shutil.ignore_patterns("*.tmp.*"))
        def build():
            return subprocess.run(["lake", "build", "ZlibF.Proof.«public-crc-combine»"],
                cwd=scratch, env=env, text=True, stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT, timeout=600)
        baseline = build()
        if baseline.returncode:
            raise RuntimeError("unmutated baseline failed:\n" + baseline.stdout)
        target = scratch / "ZlibF/Zlib/crc32.c.lean"
        original = target.read_text()
        for label, start, end, old, new in cases:
            before, rest = original.split(start, 1)
            middle, after = rest.split(end, 1)
            if middle.count(old) != 1:
                raise RuntimeError("expected one mutation site for " + label)
            target.write_text(before + start + middle.replace(old, new) + end + after)
            result = build()
            error = re.search(r"^error: ([^\n]+)", result.stdout, re.MULTILINE)
            names = {"gen64": "gen64_neg", "gen": "crc32_combine_gen_safe",
                     "op": "combine_op_ok", "combine64": "combine64_ok", "combine": "crc32_combine_safe"}
            proof = (scratch / "ZlibF/Proof/crc32.c.lean").read_text()
            declarations = list(re.finditer(r"^theorem ([\w]+)\b", proof, re.MULTILINE))
            index = next(i for i, item in enumerate(declarations) if item.group(1) == names[label])
            start_line = proof.count("\n", 0, declarations[index].start()) + 1
            end_line = proof.count("\n", 0, declarations[index + 1].start()) + 1
            if result.returncode == 0 or error is None or not (
                error.group(1).startswith("ZlibF/Proof/crc32.c.lean:") and
                start_line <= int(error.group(1).split(":")[1]) < end_line
            ) or any(term in error.group(1) for term in ("maximum recursion depth", "timeout", "heartbeats")):
                raise RuntimeError(label + " survived or failed elsewhere:\n" + result.stdout)
            print("KILLED " + label + ": " + error.group(1), flush=True)
            target.write_text(original)


if __name__ == "__main__":
    main()
