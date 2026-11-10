#!/usr/bin/env python3
"""Synchronize DIST/DISTEXT source cuts and reject changed execution."""
from pathlib import Path
import os
import re
import shutil
import subprocess
import tempfile


def main():
    root = Path(__file__).resolve().parents[2]
    source = Path("ZlibF/Zlib/inflate.c.lean")
    lookup = Path("ZlibF/Proof/inflate.c.lookup-distance.lean")
    finish = Path("ZlibF/Proof/inflate.c.distance-finish.lean")
    extra = Path("ZlibF/Proof/inflate.c.distance-extra.lean")
    originals = {p: (root / p).read_text() for p in (source, lookup, finish, extra)}
    env = os.environ.copy()
    env["LC_ALL"] = "C"

    def run(where, args):
        return subprocess.run(args, cwd=where, env=env, text=True,
                              stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=600)

    def edit(text, begin, end, old, new):
        a = text.index(begin)
        b = text.index(end, a)
        part = text[a:b]
        if part.count(old) != 1:
            raise RuntimeError("ambiguous mutation: " + old)
        return text[:a] + part.replace(old, new) + text[b:]

    with tempfile.TemporaryDirectory(prefix="inflate-distance-chain-") as name:
        scratch = Path(name)
        for file in ("lakefile.toml", "lean-toolchain"):
            shutil.copy2(root / file, scratch / file)
        shutil.copytree(root / "ZlibF", scratch / "ZlibF")
        shutil.copytree(root / ".lake", scratch / ".lake", ignore=shutil.ignore_patterns("*.tmp.*"))
        target = "ZlibF.Proof.«inflate.c.pending-dispatch»"
        baseline = run(scratch, ["lake", "build", target])
        if baseline.returncode:
            raise RuntimeError("baseline failed:\n" + baseline.stdout)
        print("baseline: complete actual slow distance boundary checks", flush=True)
        variants = (
            ("omit-distance-leaf-drop", "leaf", "DROPBITS here.bits.toUInt32", "pure ()"),
            ("invert-invalid-distance-check", "guard", "if (here.op &&& 64) != 0 then", "if (here.op &&& 64) == 0 then"),
            ("omit-distance-extra-drop", "extra", "DROPBITS s.extra", "pure ()"),
            ("omit-distance-base-update", "extra", "offset := s.offset + b", "offset := s.offset"),
        )
        for label, stage, old, new in variants:
            for path, text in originals.items():
                (scratch / path).write_text(text)
            src = originals[source]
            if stage in ("leaf", "guard"):
                src = edit(src, "def inflate_DIST (", "/-- `case LENEXT:", old, new)
                text = edit(originals[lookup], "def distFinish (", "private theorem bindX_assoc", old, new)
                (scratch / lookup).write_text(text)
                if stage == "guard":
                    text = edit(originals[finish], "def distLeafTail (", "/-- Consume the actual distance leaf", old, new)
                    (scratch / finish).write_text(text)
                proof = finish
                first_decl = "theorem distFinish_consume" if stage == "leaf" else "theorem distLeafTail_boundary"
                end_decl = "theorem distLeafTail_boundary" if stage == "leaf" else "end Zlib.Inflate.Proofs"
            else:
                src = edit(src, "def inflate_DISTEXT (", "/-- The two-level table lookup", old, new)
                cut_old = "DROPBITS extra" if "DROPBITS" in old else old
                text = edit(originals[extra], "def distExtraNeed (", "/-- The nonzero-extra source cut", cut_old, new)
                (scratch / extra).write_text(text)
                proof = extra
                first_decl = "theorem inflate_DISTEXT_boundary"
                end_decl = "end Zlib.Inflate.Proofs"
            (scratch / source).write_text(src)
            result = run(scratch, ["lake", "build", target])
            first = re.search(r"^error: ([^\n]+)", result.stdout, re.MULTILINE)
            hit = re.match(re.escape(str(proof)) + r":(\d+):", first.group(1)) if first else None
            text = (scratch / proof).read_text()
            a = text[:text.index(first_decl)].count("\n") + 1
            b = text[:text.index(end_decl)].count("\n") + 1
            exhausted = any(word in result.stdout.lower() for word in (
                "maximum recursion depth", "maximum number of heartbeats", "deterministic timeout"))
            if result.returncode == 0 or hit is None or not a <= int(hit.group(1)) < b or exhausted:
                raise RuntimeError(label + " survived or failed elsewhere:\n" + result.stdout)
            if stage in ("leaf", "guard"):
                checked = run(scratch, ["lake", "build", "ZlibF.Proof.«inflate.c.lookup-distance»"])
            else:
                cut = text.split("/-- Actual DISTEXT", 1)[0]
                (scratch / "DistanceExtraCutpoint.lean").write_text(cut + "\nend Zlib.Inflate.Proofs\n")
                checked = run(scratch, ["lake", "env", "lean", "DistanceExtraCutpoint.lean"])
            if checked.returncode:
                raise RuntimeError("synchronized actual source cuts failed:\n" + checked.stdout)
            print("KILLED " + label + ": " + first.group(1) + "; source cut still checks", flush=True)


if __name__ == "__main__":
    main()
