#!/usr/bin/env python3
"""A valid but wrong header permutation keeps safety and breaks format meaning."""
from pathlib import Path
import os
import re
import shutil
import subprocess
import tempfile


def main():
    root = Path(__file__).resolve().parents[2]
    source = Path("ZlibF/Zlib/inflate.c.lean")
    meaning = Path("ZlibF/Math/inflate-header-alphabet.lean")
    original = (root / source).read_text()
    old = "def order : Array UInt16 := #[16, 17, 18,"
    new = "def order : Array UInt16 := #[17, 16, 18,"
    if original.count(old) != 1:
        raise RuntimeError("ambiguous header permutation mutation")
    environment = os.environ.copy()
    environment["LC_ALL"] = "C"

    def run(where, args):
        return subprocess.run(args, cwd=where, env=environment, text=True,
                              stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=600)

    with tempfile.TemporaryDirectory(prefix="inflate-header-alphabet-") as name:
        scratch = Path(name)
        for file in ("lakefile.toml", "lean-toolchain"):
            shutil.copy2(root / file, scratch / file)
        shutil.copytree(root / "ZlibF", scratch / "ZlibF")
        shutil.copytree(root / ".lake", scratch / ".lake", ignore=lambda path, names:
                        {"bin"} if Path(path).resolve() == (root / ".lake/build").resolve()
                        else {n for n in names if ".tmp." in n})
        target = "ZlibF.Proof.«inflate.c.header-alphabet»"
        safety_target = "ZlibF.Proof.«inflate.c.lenlens-mode»"
        baseline = run(scratch, ["lake", "build", target, safety_target])
        if baseline.returncode:
            raise RuntimeError("baseline failed:\n" + baseline.stdout)
        print("baseline: actual LENLENS safety and independent alphabet bridge check", flush=True)
        (scratch / source).write_text(original.replace(old, new))
        safety = run(scratch, ["lake", "build", safety_target])
        if safety.returncode:
            raise RuntimeError("permuted source safety failed:\n" + safety.stdout)
        print("mutant: complete original LENLENS safety and source equalities still check", flush=True)
        result = run(scratch, ["lake", "build", target])
        first = re.search(r"^error: ([^\n]+)", result.stdout, re.MULTILINE)
        hit = re.match(re.escape(str(meaning)) + r":(\d+):", first.group(1)) if first else None
        text = (scratch / meaning).read_text()
        start = text[:text.index("theorem orderNat_format_inverse")].count("\n") + 1
        end = text[:text.index("theorem format_orderNat_inverse")].count("\n") + 1
        exhausted = any(word in result.stdout.lower() for word in (
            "maximum recursion depth", "maximum number of heartbeats", "deterministic timeout"))
        if result.returncode == 0 or hit is None or not start <= int(hit.group(1)) < end or exhausted:
            raise RuntimeError("wrong permutation survived or failed elsewhere:\n" + result.stdout)
        print("KILLED wrong-header-permutation: " + first.group(1), flush=True)
        (scratch / source).write_text(original)
        restored = run(scratch, ["lake", "build", target, safety_target])
        if restored.returncode:
            raise RuntimeError("restored positive failed:\n" + restored.stdout)
        print("restored positive: actual safety and independent alphabet bridge check", flush=True)


if __name__ == "__main__":
    main()
