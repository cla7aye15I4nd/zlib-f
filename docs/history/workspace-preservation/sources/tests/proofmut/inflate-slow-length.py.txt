#!/usr/bin/env python3
"""Keep actual slow LEN cuts synchronized and reject wrong leaf consumption."""
from pathlib import Path
import os
import re
import shutil
import subprocess
import tempfile


def main():
    root = Path(__file__).resolve().parents[2]
    source = Path("ZlibF/Zlib/inflate.c.lean")
    cuts = Path("ZlibF/Proof/inflate.c.lookup-length.lean")
    proof = Path("ZlibF/Proof/inflate.c.length-finish.lean")
    originals = {p: (root / p).read_text() for p in (source, cuts, proof)}
    env = os.environ.copy()
    env["LC_ALL"] = "C"

    def run(where, args):
        return subprocess.run(args, cwd=where, env=env, text=True,
                              stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=600)

    def replace_part(text, begin, end, old, new):
        a = text.index(begin)
        b = text.index(end, a)
        part = text[a:b]
        if part.count(old) != 1:
            raise RuntimeError("ambiguous mutation: " + old)
        return text[:a] + part.replace(old, new) + text[b:]

    with tempfile.TemporaryDirectory(prefix="inflate-slow-length-") as name:
        scratch = Path(name)
        for file in ("lakefile.toml", "lean-toolchain"):
            shutil.copy2(root / file, scratch / file)
        shutil.copytree(root / "ZlibF", scratch / "ZlibF")
        shutil.copytree(root / ".lake", scratch / ".lake", ignore=shutil.ignore_patterns("*.tmp.*"))
        target = "ZlibF.Proof.«inflate.c.pending-dispatch»"
        baseline = run(scratch, ["lake", "build", target])
        if baseline.returncode:
            raise RuntimeError("baseline failed:\n" + baseline.stdout)
        print("baseline: complete actual slow LEN boundary checks", flush=True)
        variants = (
            ("omit-leaf-bit-consumption", "DROPBITS here.bits.toUInt32", "pure ()", False),
            ("wrong-back-increment", "chkI32 (s.back.toInt + here.bits.toNat)",
             "chkI32 (s.back.toInt + here.bits.toNat + 1)", False),
            ("wrong-literal-mode", "setMode c.st LIT", "setMode c.st MATCH", True),
        )
        proof_text = (root / proof).read_text()
        first_line = proof_text[:proof_text.index("theorem lenFinish_consume")].count("\n") + 1
        last_line = proof_text[:proof_text.index("theorem back_ofNat_small")].count("\n") + 1
        for label, old, new, classify in variants:
            for path, text in originals.items():
                if path == source:
                    changed = replace_part(text, "def inflate_LEN (", "/-- `case LEN_:", old, new)
                elif path == cuts:
                    changed = replace_part(text, "def lenFinish (", "def lenSlow (", old, new)
                    changed = replace_part(changed, "def lenSlow (", "private theorem bindX_assoc", old, new)
                else:
                    changed = replace_part(text, "def lenLeafTail (", "/-- Consume the actual selected leaf", old, new) if classify else text
                (scratch / path).write_text(changed)
            equality = run(scratch, ["lake", "build", "ZlibF.Proof.«inflate.c.lookup-length»"])
            if equality.returncode:
                raise RuntimeError("synchronized actual source cuts failed:\n" + equality.stdout)
            result = run(scratch, ["lake", "build", target])
            first = re.search(r"^error: ([^\n]+)", result.stdout, re.MULTILINE)
            hit = re.match(re.escape(str(proof)) + r":(\d+):", first.group(1)) if first else None
            exhausted = any(word in result.stdout.lower() for word in (
                "maximum recursion depth", "maximum number of heartbeats", "deterministic timeout"))
            a = proof_text[:proof_text.index("theorem lenLeafTail_boundary")].count("\n") + 1 if classify else first_line
            b = proof_text[:proof_text.index("theorem inflate_LEN_slow_boundary")].count("\n") + 1 if classify else last_line
            if result.returncode == 0 or hit is None or not a <= int(hit.group(1)) < b or exhausted:
                raise RuntimeError(label + " survived or failed elsewhere:\n" + result.stdout)
            print("KILLED " + label + ": " + first.group(1) + "; actual source cuts still check", flush=True)


if __name__ == "__main__":
    main()
