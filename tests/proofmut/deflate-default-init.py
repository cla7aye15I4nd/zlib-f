#!/usr/bin/env python3
"""Check the exact default-init proof and two synchronized execution mutants.

The temporary registry selects a locally proved theorem. It does not add
the result to the reviewed audit registry. Resource failures never count
as a proof rejection.
"""
from pathlib import Path
import os
import re
import shutil
import subprocess
import tempfile


def main():
    root = Path(__file__).resolve().parents[2]
    source = Path("ZlibF/Zlib/deflate.c.lean")
    fragment = Path("ZlibF/Proof/deflate.c.init.default.lean")
    module = "ZlibF.Proof.«public-deflate-init»"
    theorem = "ZlibF.Spec.Public.Proofs.DeflateInit.deflateInit_proof"
    goal = "ZlibF.Spec.Public.Goal.deflateInit_"
    lake = shutil.which("lake") or str(Path.home() / ".elan/bin/lake")
    env = dict(os.environ, LC_ALL="C")

    def run(where, arguments):
        return subprocess.run([lake, *arguments], cwd=where, env=env, text=True,
                              stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                              timeout=180)

    def success(result, label):
        if result.returncode:
            raise RuntimeError(label + ":\n" + result.stdout)

    def reject_resources(result):
        words = ("maximum recursion depth", "maximum number of heartbeats",
                 "deterministic timeout", "interrupted", "out of memory")
        if any(word in result.stdout.lower() for word in words):
            raise RuntimeError("resource failure is inconclusive:\n" + result.stdout)

    success(run(root, ["build", module]), "positive proof build")
    original_source = (root / source).read_text()
    original_fragment = (root / fragment).read_text()
    with tempfile.TemporaryDirectory(prefix="deflate-default-init-") as directory:
        scratch = Path(directory)
        for file in ("lakefile.toml", "lean-toolchain"):
            shutil.copy2(root / file, scratch / file)
        shutil.copytree(root / "ZlibF", scratch / "ZlibF")
        shutil.copytree(root / ".lake/build", scratch / ".lake/build")
        registry = scratch / "registry.txt"
        registry.write_text(theorem + "\n")
        original_library = str(root / ".lake/build/lib/lean")
        changed_library = str(scratch / ".lake/build/lib/lean")
        replay = ["env", "lean", "--run", str(root / "tests/audit/ReplayPublicProof.lean"),
                  original_library, changed_library, "ZlibF.Zlib.«deflate.c»", goal, str(registry)]
        success(run(scratch, replay), "positive exact-proof kernel replay")
        print("baseline: exact public proof replays in a fresh kernel", flush=True)

        wrapper = "deflateInit2_ strm level Z_DEFLATED MAX_WBITS DEF_MEM_LEVEL Z_DEFAULT_STRATEGY version stream_size"
        cases = (
            ("stream-forwarding", wrapper, wrapper.replace("strm level", "none level")),
            ("version-forwarding", wrapper, wrapper.replace("version stream_size", ".null stream_size")),
            ("size-forwarding", wrapper, wrapper.replace("version stream_size", "version 0")),
            ("symbol-limit", "sym_end := (lit_bufsize - 1) * 3",
             "sym_end := (lit_bufsize - 2) * 3"),
            ("failure-cleanup", "let _ ← deflateEnd strm", "let _ ← pure Z_OK"),
        )
        for label, old, new in cases:
            if original_source.count(old) != 1:
                raise RuntimeError("ambiguous source mutation: " + label)
            (scratch / source).write_text(original_source.replace(old, new))
            (scratch / fragment).write_text(original_fragment)
            success(run(scratch, ["build", "ZlibF.Zlib.«deflate.c»"]),
                    label + " source must compile")
            if label not in ("symbol-limit", "failure-cleanup"):
                result = run(scratch, replay)
                reject_resources(result)
                if result.returncode != 2 or "EXACT_PROOF_REJECTED: " + theorem not in result.stdout:
                    raise RuntimeError(label + " survived or replay failed inconclusively:\n" + result.stdout)
                print("KILLED " + label + ": original exact public proof rejected", flush=True)
                continue
            if label == "symbol-limit":
                synchronized = original_fragment.replace("sym_end := 49149", "sym_end := 49146")
                expected = "ZlibF/Proof/deflate.c.init.success.lean"
                first_theorem, next_theorem = "theorem finish_to_reset", "theorem ready_storage"
            else:
                synchronized = original_fragment.replace("let _ ← deflateEnd strm", "let _ ← pure Z_OK")
                expected = "ZlibF/Proof/deflate.c.init.failure.lean"
                first_theorem, next_theorem = "theorem finish_failure", "theorem slot_clearD_except"
            (scratch / fragment).write_text(synchronized)
            success(run(scratch, ["build", "ZlibF.Proof.«deflate.c.init.default»"]),
                    label + " synchronized whole-source equality")
            result = run(scratch, ["build", module])
            reject_resources(result)
            first = re.search(r"^error: ([^\n]+)", result.stdout, re.MULTILINE)
            hit = re.match(re.escape(expected) + r":(\d+):", first.group(1)) if first else None
            text = (root / expected).read_text()
            start = text[:text.index(first_theorem)].count("\n") + 1
            end = text[:text.index(next_theorem)].count("\n") + 1
            if (result.returncode == 0 or hit is None or not start <= int(hit.group(1)) < end
                    or not any(word in result.stdout.lower() for word in ("type mismatch", "not definitionally equal"))):
                raise RuntimeError(label + " lacked a local execution-proof rejection:\n" + result.stdout)
            print("KILLED " + label + ": whole-source equality checks; " + first.group(1), flush=True)


if __name__ == "__main__":
    main()
