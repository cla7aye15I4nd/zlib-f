#!/usr/bin/env python3
"""Synchronize constructor cutpoints; reject wrong decoder cells in proofs."""
from pathlib import Path
import os
import re
import shutil
import subprocess
import tempfile


def main():
    root = Path(__file__).resolve().parents[2]
    source = Path("ZlibF/Zlib/inftrees.c.lean")
    base = Path("ZlibF/Proof/inftrees.c.base.lean")
    step = Path("ZlibF/Proof/inftrees.c.step.lean")
    outer = Path("ZlibF/Proof/inftrees.c.main.lean")
    tail = Path("ZlibF/Proof/inftrees.c.content.tail.lean")
    originals = {p: (root / p).read_text() for p in (source, base, step, outer, tail)}
    env = os.environ.copy()
    env["LC_ALL"] = "C"

    def run(where, args):
        return subprocess.run(args, cwd=where, env=env, text=True,
                              stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=600)

    def replace_once(text, old, new):
        if text.count(old) != 1:
            raise RuntimeError("ambiguous mutation site: " + old)
        return text.replace(old, new, 1)

    with tempfile.TemporaryDirectory(prefix="inflate-table-decoder-") as name:
        scratch = Path(name)
        for file in ("lakefile.toml", "lean-toolchain"):
            shutil.copy2(root / file, scratch / file)
        shutil.copytree(root / "ZlibF", scratch / "ZlibF")
        shutil.copytree(root / ".lake", scratch / ".lake", ignore=shutil.ignore_patterns("*.tmp.*"))
        target = "ZlibF.Proof.«inftrees.c.read-extent»"
        baseline = run(scratch, ["lake", "build", target])
        if baseline.returncode:
            raise RuntimeError("baseline failed:\n" + baseline.stdout)
        print("baseline: decoder safety and returned extent check", flush=True)
        for label in ("literal-becomes-link", "singleton-invalid-zero-bits"):
            for path, text in originals.items():
                (scratch / path).write_text(text)
            if label == "literal-becomes-link":
                old = "s := { s with here := { s.here with op := 0 } }"
                new = "s := { s with here := { s.here with op := 1 } }"
                for path in (source, base):
                    (scratch / path).write_text(replace_once(originals[path], old, new))
                text = replace_once(originals[step], "then ⟨0, bits, w⟩", "then ⟨1, bits, w⟩")
                (scratch / step).write_text(text)
                expected = "ZlibF/Proof/inftrees.c.content.codes.lean"
            else:
                old = "⟨64, (s.len - s.drop).toUInt8, 0⟩"
                new = "⟨64, 0, 0⟩"
                (scratch / source).write_text(replace_once(originals[source], old, new))
                if originals[outer].count(old) != 3:
                    raise RuntimeError("unexpected original tail-store proof shape")
                (scratch / outer).write_text(originals[outer].replace(old, new))
                # Synchronize all concrete tail-store expressions, retaining
                # the theorem's required one-bit invalid-cell conclusion.
                text = originals[tail]
                if text.count(old) != 2:
                    raise RuntimeError("unexpected tail-store proof shape")
                (scratch / tail).write_text(text.replace(old, new))
                expected = "ZlibF/Proof/inftrees.c.content.tail.lean"
            result = run(scratch, ["lake", "build", target])
            first = re.search(r"^error: ([^\n]+)", result.stdout, re.MULTILINE)
            exhausted = any(word in result.stdout.lower() for word in (
                "maximum recursion depth", "maximum number of heartbeats", "deterministic timeout"))
            if result.returncode == 0 or first is None or not first.group(1).startswith(expected + ":") or exhausted:
                raise RuntimeError(label + " survived or failed elsewhere:\n" + result.stdout)
            # Complete source/cutpoint equality must still check under each
            # synchronized mutation; a mere source-equality failure is insufficient.
            cut = (scratch / outer).read_text().split("theorem gaddr0", 1)[0]
            (scratch / "ConstructorCutpoint.lean").write_text(cut +
                "\ntheorem inflate_table_eq : inflate_table = itTop := rfl\n" +
                "\nend Zlib.Inftrees.Proofs\n")
            checked = run(scratch, ["lake", "env", "lean", "ConstructorCutpoint.lean"])
            if checked.returncode:
                raise RuntimeError("synchronized cutpoint check failed:\n" + checked.stdout)
            print("KILLED " + label + ": " + first.group(1) + "; cutpoints still check", flush=True)


if __name__ == "__main__":
    main()
