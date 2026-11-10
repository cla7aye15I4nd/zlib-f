#!/usr/bin/env python3
"""Check dispatch entry and generic literal execution against direct mutants.

The scratch baseline and mutants omit the earlier block-only literal proof
and raw-call entry proofs. This isolates rejection in the new execution
proofs. No checkout proof or registry is changed or replaced by an assumption.
"""
from pathlib import Path
import os
import re
import shutil
import subprocess
import tempfile


def main():
    root = Path(__file__).resolve().parents[2]
    source = Path("ZlibF/Zlib/inflate.c.lean")
    original = (root / source).read_text()
    literal = Path("ZlibF/Proof/inflate.c.literal-step.lean")
    entry = Path("ZlibF/Proof/inflate.c.dispatch-entry.lean")
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

    with tempfile.TemporaryDirectory(prefix="inflate-dispatch-buffers-") as name:
        scratch = Path(name)
        for file in ("lakefile.toml", "lean-toolchain"):
            shutil.copy2(root / file, scratch / file)
        shutil.copytree(root / "ZlibF", scratch / "ZlibF")
        shutil.copytree(root / ".lake", scratch / ".lake", ignore=shutil.ignore_patterns("*.tmp.*"))
        # Both the positive control and every mutant use the same isolation.
        simple = scratch / "ZlibF/Proof/inflate.c.main.simple.lean"
        text = simple.read_text()
        simple.write_text(text[:text.index("/-- `case LIT:` with room")] + "\nend Zlib.Inflate.Proofs\n")
        stored = scratch / "ZlibF/Proof/inflate.c.stored-call.lean"
        text = stored.read_text()
        a = text.index("theorem inflate_run_raw_copy")
        a = text.rindex("/--", 0, a)
        stored.write_text(text[:a] + "\nend Zlib.Inflate.Proofs\n")
        targets = ("ZlibF.Proof.«inflate.c.literal-step»", "ZlibF.Proof.«inflate.c.dispatch-entry»",
                   "ZlibF.Proof.«inflate.c.pending-entry»")
        baseline = run(scratch, ["lake", "build", *targets])
        if baseline.returncode:
            raise RuntimeError("isolated baseline failed:\n" + baseline.stdout)
        print("baseline: actual dispatch entry and generic literal step check without older overlapping proofs", flush=True)
        variants = (
            ("literal-wrong-byte", "literal", "s.length.toUInt8", "(s.length + 1).toUInt8"),
            ("literal-wrong-advance", "literal", "l.put.add 1", "l.put.add 2"),
            ("literal-omit-decrement", "literal", "left := l.left - 1", "left := l.left"),
            ("literal-wrong-mode", "literal", "setMode c.st LEN", "setMode c.st MATCH"),
            ("entry-wrong-output-count", "entry", "out_ := l.left", "out_ := l.left + 1"),
            ("entry-wrong-input-count", "entry", "in_ := l.have_", "in_ := l.have_ - 1"),
            ("entry-wrong-return-code", "entry", "ret := Z_OK", "ret := Z_BUF_ERROR"),
            ("entry-omit-type-normalization", "entry", "then setMode c.st TYPEDO", "then setMode c.st TYPE"),
        )
        for label, stage, old, new in variants:
            if stage == "literal":
                text = edit(original, "def inflate_LIT (", "/-- `case MATCH:", old, new)
                proof, begin, end = literal, "theorem inflate_LIT_view_run", "theorem inflate_LIT_step"
            else:
                text = edit(original, "def inflate_run (", "/-- `inf_leave:", old, new)
                proof, begin, end = entry, "theorem inflate_run_output_entry_frame", "theorem inflate_run_output_entry "
            (scratch / source).write_text(text)
            result = run(scratch, ["lake", "build", *targets])
            first = re.search(r"^error: ([^\n]+)", result.stdout, re.MULTILINE)
            hit = re.match(re.escape(str(proof)) + r":(\d+):", first.group(1)) if first else None
            proof_text = (scratch / proof).read_text()
            a = proof_text[:proof_text.index(begin)].count("\n") + 1
            b = proof_text[:proof_text.index(end)].count("\n") + 1
            exhausted = any(word in result.stdout.lower() for word in (
                "maximum recursion depth", "maximum number of heartbeats", "deterministic timeout"))
            if result.returncode == 0 or hit is None or not a <= int(hit.group(1)) < b or exhausted:
                raise RuntimeError(label + " survived or failed elsewhere:\n" + result.stdout)
            print("KILLED " + label + ": " + first.group(1), flush=True)


if __name__ == "__main__":
    main()
