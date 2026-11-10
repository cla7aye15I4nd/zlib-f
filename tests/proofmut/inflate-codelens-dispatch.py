#!/usr/bin/env python3
"""Synchronize actual CODELENS checks and cuts; reject broken dispatch."""
from pathlib import Path
import os
import re
import shutil
import subprocess
import tempfile


def main():
    root = Path(__file__).resolve().parents[2]
    source = Path("ZlibF/Zlib/inflate.c.lean")
    dynamic = Path("ZlibF/Proof/inflate.c.dynamic-install.lean")
    proof = Path("ZlibF/Proof/inflate.c.codelens-dispatch.lean")
    originals = {p: (root / p).read_text() for p in (source, dynamic)}
    env = os.environ.copy()
    env["LC_ALL"] = "C"

    def run(where, args):
        return subprocess.run(args, cwd=where, env=env, text=True,
                              stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=600)

    with tempfile.TemporaryDirectory(prefix="inflate-codelens-dispatch-") as name:
        scratch = Path(name)
        for file in ("lakefile.toml", "lean-toolchain"):
            shutil.copy2(root / file, scratch / file)
        shutil.copytree(root / "ZlibF", scratch / "ZlibF")
        shutil.copytree(root / ".lake", scratch / ".lake", ignore=shutil.ignore_patterns("*.tmp.*"))
        target = "ZlibF.Proof.«inflate.c.codelens-dispatch»"
        baseline = run(scratch, ["lake", "build", target])
        if baseline.returncode:
            raise RuntimeError("baseline failed:\n" + baseline.stdout)
        print("baseline: complete actual CODELENS boundary checks", flush=True)
        variants = (
            ("wrong-bad-mode-guard", "if (← rdS c.st (·.mode)) == BAD then return",
             "if (← rdS c.st (·.mode)) == MEM then return"),
            ("invert-end-of-block-check", "if (← Ptr.index (lensP c.st) 256) == (0 : UInt16) then",
             "if (← Ptr.index (lensP c.st) 256) != (0 : UInt16) then"),
        )
        text = (root / proof).read_text()
        a = text[:text.index("theorem clTail_run_good")].count("\n") + 1
        b = text[:text.index("theorem inflate_CODELENS_boundary")].count("\n") + 1
        for label, old, new in variants:
            for path, text in originals.items():
                begin = text.index("def inflate_CODELENS" if path == source else "def clTail (")
                end = text.index("/-- `case LENLENS:" if path == source else "theorem inflate_CODELENS_eq", begin)
                part = text[begin:end]
                if part.count(old) != 1:
                    raise RuntimeError("ambiguous mutation: " + old)
                (scratch / path).write_text(text[:begin] + part.replace(old, new) + text[end:])
            result = run(scratch, ["lake", "build", target])
            first = re.search(r"^error: ([^\n]+)", result.stdout, re.MULTILINE)
            hit = re.match(re.escape(str(proof)) + r":(\d+):", first.group(1)) if first else None
            exhausted = any(word in result.stdout.lower() for word in (
                "maximum recursion depth", "maximum number of heartbeats", "deterministic timeout"))
            if result.returncode == 0 or hit is None or not a <= int(hit.group(1)) < b or exhausted:
                raise RuntimeError(label + " survived or failed elsewhere:\n" + result.stdout)
            cut = (scratch / dynamic).read_text().split("def clLensPre", 1)[0]
            (scratch / "CodelensCutpoint.lean").write_text(cut + "\nend Zlib.Inflate.Proofs\n")
            checked = run(scratch, ["lake", "env", "lean", "CodelensCutpoint.lean"])
            if checked.returncode:
                raise RuntimeError("synchronized CODELENS equality failed:\n" + checked.stdout)
            print("KILLED " + label + ": " + first.group(1) + "; source equality still checks", flush=True)


if __name__ == "__main__":
    main()
