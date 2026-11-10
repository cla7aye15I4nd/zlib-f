#!/usr/bin/env python3
"""Synchronize actual DIST source cuts and reject broken root consumption."""
from pathlib import Path
import os
import re
import shutil
import subprocess
import tempfile


def main():
    root = Path(__file__).resolve().parents[2]
    source = Path("ZlibF/Zlib/inflate.c.lean")
    proof = Path("ZlibF/Proof/inflate.c.lookup-distance.lean")
    originals = {p: (root / p).read_text() for p in (source, proof)}
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

    with tempfile.TemporaryDirectory(prefix="inflate-distance-lookup-") as name:
        scratch = Path(name)
        for file in ("lakefile.toml", "lean-toolchain"):
            shutil.copy2(root / file, scratch / file)
        shutil.copytree(root / "ZlibF", scratch / "ZlibF")
        shutil.copytree(root / ".lake", scratch / ".lake", ignore=shutil.ignore_patterns("*.tmp.*"))
        target = "ZlibF.Proof.«inflate.c.lookup-distance»"
        baseline = run(scratch, ["lake", "build", target])
        if baseline.returncode:
            raise RuntimeError("baseline failed:\n" + baseline.stdout)
        print("baseline: actual DIST lookup boundary checks", flush=True)
        variants = (
            ("omit-distance-root-drop", "DROPBITS last.bits.toUInt32", "pure ()"),
            ("wrong-distance-root-back", "chkI32 (s.back.toInt + last.bits.toNat)",
             "chkI32 (s.back.toInt + last.bits.toNat + 1)"),
        )
        for label, old, new in variants:
            changed_source = replace_part(originals[source], "def inflate_DIST (", "/-- `case LENEXT:", old, new)
            text = replace_part(originals[proof], "def distSubLookup (", "/-- Actual second-level distance lookup", old, new)
            text = replace_part(text, "def distRootTail (", "def distLookup (", old, new)
            (scratch / source).write_text(changed_source)
            (scratch / proof).write_text(text)
            result = run(scratch, ["lake", "build", target])
            first = re.search(r"^error: ([^\n]+)", result.stdout, re.MULTILINE)
            hit = re.match(re.escape(str(proof)) + r":(\d+):", first.group(1)) if first else None
            a = text[:text.index("theorem distSubLookup_run")].count("\n") + 1
            b = text[:text.index("/-- The distance decoder's actual root-link test")].count("\n") + 1
            exhausted = any(word in result.stdout.lower() for word in (
                "maximum recursion depth", "maximum number of heartbeats", "deterministic timeout"))
            if result.returncode == 0 or hit is None or not a <= int(hit.group(1)) < b or exhausted:
                raise RuntimeError(label + " survived or failed elsewhere:\n" + result.stdout)
            cut = text[:text.index("/-- The actual slow distance-link block")]
            cut += text[text.index("def distSubLookup ("):text.index("/-- Actual second-level distance lookup")]
            cut += text[text.index("def distRootTail ("):text.index("theorem distRootTail_link")]
            cut += text[text.index("def distFinish ("):text.index("/-- Actual DIST lookup uses")]
            (scratch / "DistanceLookupCutpoint.lean").write_text(cut + "\nend Zlib.Inflate.Proofs\n")
            checked = run(scratch, ["lake", "env", "lean", "DistanceLookupCutpoint.lean"])
            if checked.returncode:
                raise RuntimeError("synchronized actual DIST cut failed:\n" + checked.stdout)
            print("KILLED " + label + ": " + first.group(1) + "; actual source cut still checks", flush=True)


if __name__ == "__main__":
    main()
