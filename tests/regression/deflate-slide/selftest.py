#!/usr/bin/env python3
"""Require the slide regression to reject the former unchecked subtraction."""

from pathlib import Path
import os
import shutil
import subprocess
import tempfile


def main():
    workspace = Path(__file__).resolve().parents[3]
    expected = [
        "block_start=-512 strstart=250 high_water=508",
        "block_start=-9223372036854775808 strstart=250 high_water=508",
        "block_start=9223372036854775295 strstart=250 high_water=508",
        "UB: signed long overflow",
    ]
    env = os.environ.copy()
    env["LC_ALL"] = "C"

    def execute(directory):
        result = subprocess.run(
            ["lake", "build", "ZlibF.Zlib.«deflate_base.c»"], cwd=directory,
            env=env, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=600,
        )
        if result.returncode:
            raise RuntimeError("translation build failed:\n" + result.stdout)
        result = subprocess.run(
            ["lake", "env", "lean", "--run", "slide.lean"], cwd=directory,
            env=env, text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=600,
        )
        if result.returncode or result.stderr:
            raise RuntimeError("regression execution failed:\n" + result.stdout + result.stderr)
        return result.stdout.splitlines()

    with tempfile.TemporaryDirectory(prefix="deflate-slide-regression-") as name:
        scratch = Path(name)
        for file in ("lakefile.toml", "lean-toolchain"):
            shutil.copy2(workspace / file, scratch / file)
        shutil.copy2(workspace / "tests/regression/deflate-slide/slide.lean", scratch / "slide.lean")
        shutil.copytree(workspace / "ZlibF", scratch / "ZlibF")
        shutil.copytree(workspace / ".lake", scratch / ".lake")
        if execute(scratch) != expected:
            raise RuntimeError("unmutated regression did not match its expected observations")
        print("baseline: defined boundaries and the overflow fault match", flush=True)
        path = scratch / "ZlibF/Zlib/deflate_base.c.lean"
        text = path.read_text()
        old = "let block_start ← lsub (← rd s (·.block_start)) wsize.toUInt64.toInt64"
        new = "let block_start := (← rd s (·.block_start)) - wsize.toUInt64.toInt64"
        if text.count(old) != 1:
            raise RuntimeError("the checked subtraction replacement is not unique")
        path.write_text(text.replace(old, new))
        mutated = execute(scratch)
        if mutated == expected or mutated[:3] != expected[:3]:
            raise RuntimeError("the regression did not isolate the unchecked overflow:\n" + "\n".join(mutated))
        if mutated[3:] != ["block_start=9223372036854775296 strstart=250 high_water=508"]:
            raise RuntimeError("unexpected mutated overflow result:\n" + "\n".join(mutated))
        print("KILLED unchecked slide subtraction: only the overflow observation changed")


if __name__ == "__main__":
    main()
