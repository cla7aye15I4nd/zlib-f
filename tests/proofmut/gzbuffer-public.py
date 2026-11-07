#!/usr/bin/env python3
"""Check the public gzbuffer proof against actual translation mutations."""
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
        ("null-result", "if file.isNone then return -1", "if file.isNone then return 0"),
        ("mode-guard", "if s.mode != GZ_READ && s.mode != GZ_WRITE then return -1", "if false then return -1"),
        ("allocation-guard", "if s.size != 0 then return -1", "if false then return -1"),
        ("overflow-guard", "if (size <<< 1) < size then return -1", "if false then return -1"),
        ("minimum-size", "if size < 8 then 8 else size", "if size < 8 then 7 else size"),
        ("change-path", "{ s with want := size }", "{ s with want := size, path := .null }"),
    )
    with tempfile.TemporaryDirectory(prefix="gzbuffer-public-mutants-") as name:
        scratch = Path(name)
        for file in ("lakefile.toml", "lean-toolchain"):
            shutil.copy2(root / file, scratch / file)
        shutil.copytree(root / "ZlibF", scratch / "ZlibF")
        shutil.copytree(root / ".lake", scratch / ".lake",
                        ignore=shutil.ignore_patterns("*.tmp.*"))

        def build():
            return subprocess.run(["lake", "build", "ZlibF.Proof.«public-gzbuffer»"],
                                  cwd=scratch, env=env, text=True,
                                  stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                  timeout=600)

        baseline = build()
        if baseline.returncode:
            raise RuntimeError("unmutated baseline failed:\n" + baseline.stdout)
        print("BASELINE PASS", flush=True)
        target = scratch / "ZlibF/Zlib/gzlib.c.lean"
        original = target.read_text()
        prefix, rest = original.split("def gzbuffer (", 1)
        body, suffix = rest.split('/-- `int ZEXPORT gzrewind', 1)
        for label, old, new in cases:
            if body.count(old) != 1:
                raise RuntimeError("expected one mutation site for " + label)
            target.write_text(prefix + "def gzbuffer (" + body.replace(old, new, 1) +
                              '/-- `int ZEXPORT gzrewind' + suffix)
            result = build()
            errors = re.findall(r"^error: ([^\n]+)", result.stdout, re.MULTILINE)
            proof_errors = [e for e in errors if e.startswith("ZlibF/Proof/public-gzbuffer.lean:")]
            if result.returncode == 0 or not proof_errors:
                raise RuntimeError(label + " survived or failed outside the function proof:\n" + result.stdout)
            print("KILLED " + label + ": " + proof_errors[0], flush=True)
            target.write_text(original)


if __name__ == "__main__":
    main()
