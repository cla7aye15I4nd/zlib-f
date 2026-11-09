#!/usr/bin/env python3
"""Keep repeat safety/cutpoints valid while corrupting extra-bit meaning."""
from pathlib import Path
import os
import re
import shutil
import subprocess
import tempfile


def main():
    root = Path(__file__).resolve().parents[2]
    source = Path("ZlibF/Zlib/inflate.c.lean")
    install = Path("ZlibF/Proof/inflate.c.dynamic-install.lean")
    step = Path("ZlibF/Proof/inflate.c.codelens-step.lean")
    semantic = Path("ZlibF/Proof/inflate.c.code-length-repeat-meaning.lean")
    originals = {p: (root / p).read_text() for p in (source, install, step, semantic)}
    environment = os.environ.copy()
    environment["LC_ALL"] = "C"

    def run(where, args):
        return subprocess.run(args, cwd=where, env=environment, text=True,
                              stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=600)

    def replace_count(text, old, new, count):
        if text.count(old) != count:
            raise RuntimeError("ambiguous mutation site: " + old)
        return text.replace(old, new)

    with tempfile.TemporaryDirectory(prefix="code-length-repeat-meaning-") as name:
        scratch = Path(name)
        for file in ("lakefile.toml", "lean-toolchain"):
            shutil.copy2(root / file, scratch / file)
        shutil.copytree(root / "ZlibF", scratch / "ZlibF")
        shutil.copytree(root / ".lake", scratch / ".lake", ignore=lambda path, names:
                        {"bin"} if Path(path).resolve() == (root / ".lake/build").resolve()
                        else {n for n in names if ".tmp." in n})
        target = "ZlibF.Proof.«inflate.c.code-length-loop-prefix»"
        baseline = run(scratch, ["lake", "build", target])
        if baseline.returncode:
            raise RuntimeError("baseline failed:\n" + baseline.stdout)
        print("baseline: actual complete ordinary code-length parser checks", flush=True)
        old = "len := v.toUInt32, copy := 3 + b"
        new = "len := v.toUInt32, copy := 3 + (b ^^^ 1)"
        for path, count in ((source, 1), (install, 1), (step, 2)):
            (scratch / path).write_text(replace_count(originals[path], old, new, count))
        text = (scratch / step).read_text()
        text = replace_count(text, "len := value.toUInt32, copy := 3 + bits",
                             "len := value.toUInt32, copy := 3 + (bits ^^^ 1)", 1)
        start = text.index("theorem clPrevBits_run")
        end = text.index("def clNeedDrop", start)
        scalar = text[start:end]
        scalar = replace_count(scalar,
            "let bits := l.hold.toUInt32 &&& ((1 : UInt32) <<< 2 - 1)",
            "let bits := (l.hold.toUInt32 &&& ((1 : UInt32) <<< 2 - 1)) ^^^ 1", 1)
        scalar = replace_count(scalar,
            "have bitsNat : bits.toNat = l.hold.toNat % 4 := BITS_toNat l 2 (by decide)",
            """have bitsNat : bits.toNat = (l.hold.toNat % 4) ^^^ 1 := by
    rw [UInt32.toNat_xor]
    rw [BITS_toNat l 2 (by decide), show (1 : UInt32).toNat = 1 by decide, show (2 : UInt32).toNat = 2 by decide]
  have changedBound : bits.toNat < 4 := by
    rw [bitsNat]
    exact Nat.xor_lt_two_pow (n := 2) (Nat.mod_lt _ (by decide)) (by decide)""", 1)
        (scratch / step).write_text(text[:start] + scalar + text[end:])
        meaning = replace_count(originals[semantic],
            "let bits := l.hold.toUInt32 &&& ((1 : UInt32) <<< 2 - 1)",
            "let bits := (l.hold.toUInt32 &&& ((1 : UInt32) <<< 2 - 1)) ^^^ 1", 1)
        (scratch / semantic).write_text(meaning)
        # A two-bit XOR permutes the four values, retaining the old 3..6
        # safety bound. The complete old safety loop and all synchronized
        # source equalities must still check before testing exact meaning.
        safety = run(scratch, ["lake", "build", "ZlibF.Proof.«inflate.c.codelens-loop»"])
        if safety.returncode:
            raise RuntimeError("synchronized safety/source proof failed:\n" + safety.stdout)
        print("mutant: original complete safety loop and source equalities still check", flush=True)
        # Independently check the exact execution part of the new proof,
        # with its computed intermediate state synchronized to the mutant.
        # The false bitsNat/readBits semantics are deliberately not imported.
        begin = meaning.index("  have index", meaning.index("theorem clPrevBits_read"))
        bridge = meaning.index("  have bitsNat", begin)
        execute = meaning.index("  · unfold clPrevBits", bridge)
        execute_end = meaning.index("  · change previous.toUInt32.toNat", execute)
        execution = meaning[execute:execute_end].replace("  · unfold clPrevBits", "  unfold clPrevBits", 1)
        execution = "\n".join(line[2:] if line.startswith("    ") else line for line in execution.splitlines()) + "\n"
        header = """import ZlibF.Proof.«inflate.c.codelens-step»
namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false
theorem clPrevBits_execution {c : Ctx} {l : IL} {h : Heap} {zs : Nat}
    {s : InflateState} {bs : List UInt8}
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (size : s.lens.size = 320) (nonempty : 1 ≤ s.«have».toNat) (haveBound : s.«have».toNat ≤ 320)
    (B : BitInv h l bs) (enough : 2 ≤ l.bits.toNat) :
    ∃ regs, runX (clPrevBits c s.«have») l h = .ok ((.ok (), regs), h) := by
"""
        locals = """  let prepared := { l with len := previous.toUInt32, copy := 3 + bits }
  let regs := { prepared with hold := prepared.hold >>> (2 : UInt32).toUInt64, bits := prepared.bits - 2 }
  refine ⟨regs, ?_⟩
"""
        (scratch / "RepeatSourceExecution.lean").write_text(header + meaning[begin:bridge] + locals + execution +
            "\n#print axioms clPrevBits_execution\nend Zlib.Inflate.Proofs\n")
        checked = run(scratch, ["lake", "env", "lean", "RepeatSourceExecution.lean"])
        if checked.returncode:
            raise RuntimeError("new proof's synchronized execution part failed:\n" + checked.stdout)
        print("mutant: new proof's exact source execution equality also checks", flush=True)
        result = run(scratch, ["lake", "build", target])
        error = re.search(r"^error: ([^\n]+)", result.stdout, re.MULTILINE)
        hit = re.match(re.escape(str(semantic)) + r":(\d+):", error.group(1)) if error else None
        meaning = (scratch / semantic).read_text()
        proof_start = meaning.index("theorem clPrevBits_read")
        first = meaning[:meaning.index("  have bitsNat", proof_start)].count("\n") + 1
        last = meaning[:meaning.index("  have copyNat", proof_start)].count("\n") + 1
        exhausted = any(token in result.stdout.lower() for token in (
            "maximum recursion depth", "maximum number of heartbeats", "deterministic timeout"))
        if result.returncode == 0 or hit is None or not first <= int(hit.group(1)) < last or exhausted:
            raise RuntimeError("wrong extra-bit meaning survived or failed elsewhere:\n" + result.stdout)
        print("KILLED parity-swapped-extra-bits: " + error.group(1), flush=True)
        for path, original in originals.items():
            (scratch / path).write_text(original)
        restored = run(scratch, ["lake", "build", target])
        if restored.returncode:
            raise RuntimeError("restored positive failed:\n" + restored.stdout)
        print("restored positive: complete parser meaning checks", flush=True)


if __name__ == "__main__":
    main()
