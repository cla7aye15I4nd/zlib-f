#!/usr/bin/env python3
"""Reject changed actual LENEXT execution with its source cut synchronized."""
from pathlib import Path
import os
import re
import shutil
import subprocess
import tempfile


def main():
    root = Path(__file__).resolve().parents[2]
    source = Path("ZlibF/Zlib/inflate.c.lean")
    proof = Path("ZlibF/Proof/inflate.c.length-extra.lean")
    originals = {p: (root / p).read_text() for p in (source, proof)}
    env = os.environ.copy()
    env["LC_ALL"] = "C"

    def run(where, args):
        return subprocess.run(args, cwd=where, env=env, text=True,
                              stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=600)

    with tempfile.TemporaryDirectory(prefix="inflate-length-extra-") as name:
        scratch = Path(name)
        for file in ("lakefile.toml", "lean-toolchain"):
            shutil.copy2(root / file, scratch / file)
        shutil.copytree(root / "ZlibF", scratch / "ZlibF")
        shutil.copytree(root / ".lake", scratch / ".lake", ignore=shutil.ignore_patterns("*.tmp.*"))
        target = "ZlibF.Proof.«inflate.c.pending-dispatch»"
        baseline = run(scratch, ["lake", "build", target])
        if baseline.returncode:
            raise RuntimeError("baseline failed:\n" + baseline.stdout)
        print("baseline: actual LENEXT boundary checks", flush=True)
        variants = (
            ("omit-extra-bit-consumption", "DROPBITS s.extra", "DROPBITS extra", "pure ()"),
            ("wrong-extra-back-count", "i2u s.back + s.extra", "i2u s.back + s.extra", "i2u s.back + s.extra + 1"),
        )
        for label, old_source, old_cut, new in variants:
            for path, text in originals.items():
                begin = text.index("def inflate_LENEXT (" if path == source else "def lenExtraNeed (")
                end = text.index("/-- `case LEN:`" if path == source else "/-- The nonzero-extra source cut", begin)
                part = text[begin:end]
                old = old_source if path == source else old_cut
                if part.count(old) != 1:
                    raise RuntimeError("ambiguous mutation: " + old)
                (scratch / path).write_text(text[:begin] + part.replace(old, new) + text[end:])
            text = (scratch / proof).read_text()
            result = run(scratch, ["lake", "build", target])
            first = re.search(r"^error: ([^\n]+)", result.stdout, re.MULTILINE)
            hit = re.match(re.escape(str(proof)) + r":(\d+):", first.group(1)) if first else None
            first_line = text[:text.index("theorem inflate_LENEXT_boundary")].count("\n") + 1
            exhausted = any(word in result.stdout.lower() for word in (
                "maximum recursion depth", "maximum number of heartbeats", "deterministic timeout"))
            if result.returncode == 0 or hit is None or int(hit.group(1)) < first_line or exhausted:
                raise RuntimeError(label + " survived or failed elsewhere:\n" + result.stdout)
            cut = text.split("/-- Actual LENEXT", 1)[0]
            (scratch / "LengthExtraCutpoint.lean").write_text(cut + "\nend Zlib.Inflate.Proofs\n")
            checked = run(scratch, ["lake", "env", "lean", "LengthExtraCutpoint.lean"])
            if checked.returncode:
                raise RuntimeError("synchronized source equality failed:\n" + checked.stdout)
            print("KILLED " + label + ": " + first.group(1) + "; source equality still checks", flush=True)


if __name__ == "__main__":
    main()
