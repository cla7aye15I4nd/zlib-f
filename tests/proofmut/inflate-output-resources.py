#!/usr/bin/env python3
"""Reject shifted slow writes and a dropped public local-buffer free."""
from pathlib import Path
import os
import re
import shutil
import subprocess
import sys
import tempfile


def main():
    root = Path(__file__).resolve().parents[2]
    lake = shutil.which("lake") or str(Path.home() / ".elan/bin/lake")
    relative = Path("ZlibF/Zlib/inflate.c.lean")
    original = (root / relative).read_text()
    cases = (
        ("literal-shifted-store", "  store8 l.put s.length.toUInt8",
         "  store8 (← l.put.add 1) s.length.toUInt8", "slow-output-exact-frame",
         {"inflate.c.literal-step.lean": ("inflate_LIT_view_run",),
          "inflate.c.main.simple.lean": ("inflate_LIT_run",)}),
        ("match-shifted-store", "      store8 l.put b",
         "      store8 (← l.put.add 1) b", "slow-output-exact-frame",
         {"inflate.c.match-copy.lean": ("matchCopyByte_run",)}),
        ("stored-shifted-copy", "    memcpyB l.put l.next copy.toNat",
         "    memcpyB (← l.put.add 1) l.next copy.toNat", "stored-output-exact-frame",
         {"inflate.c.main.stored.lean": ("inflate_COPY_split",),
          "inflate.c.stored-views.lean": ("inflate_COPY_views_run",)}),
        ("public-local-leak", "  freeB hbuf\n  return r",
         "  pure ()\n  return r", "live-frame-public",
         {"inflate.c.stored-call.lean": ("inflate_raw_copy_finish_run",),
          "inflate.c.default-view-public.lean": ("inflate_default_view_state_safe",),
          "inflate.c.default-view-public-memory-totals.lean": ("inflate_default_view_public_memory_totals",),
          "inflate.c.live-frame-public.lean": ("inflate_default_view_public_live",)}),
    )
    selected = set(sys.argv[1:])
    if selected - {case[0] for case in cases}:
        raise RuntimeError("unknown mutation selection")
    if selected:
        cases = tuple(case for case in cases if case[0] in selected)
    env = dict(os.environ, LC_ALL="C")
    with tempfile.TemporaryDirectory(prefix="inflate-output-resources-") as directory:
        scratch = Path(directory)
        for name in ("lakefile.toml", "lean-toolchain"):
            shutil.copy2(root / name, scratch / name)
        shutil.copytree(root / "ZlibF", scratch / "ZlibF")
        # Use a copy-on-write build snapshot when the host supports it.
        build = scratch / ".lake/build"
        build.parent.mkdir()
        cloned = subprocess.run(["cp", "-cR", str(root / ".lake/build"), str(build)],
                                stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        if cloned.returncode:
            shutil.rmtree(build, ignore_errors=True)
            shutil.copytree(root / ".lake/build", build)

        def check(target):
            return subprocess.run([lake, "build", target], cwd=scratch, env=env,
                                  text=True, stdout=subprocess.PIPE,
                                  stderr=subprocess.STDOUT, timeout=900)

        def require(result, label):
            if result.returncode:
                raise RuntimeError(label + ":\n" + result.stdout)

        for _, _, _, target, _ in cases:
            require(check("ZlibF.Proof.«inflate.c." + target + "»"), "positive complete caller")
        print("baseline: all exact-output and public-allocation callers check", flush=True)
        for label, old, new, target, proofs in cases:
            if original.count(old) != 1:
                raise RuntimeError("mutation must match exactly once: " + label)
            (scratch / relative).write_text(original.replace(old, new, 1))
            require(check("ZlibF.Zlib.«inflate.c»"), label + " translation compilation")
            synchronized = None
            if label == "match-shifted-store":
                # This source cut factors out the literal MATCH byte loop.
                # Keep its helper identical to the changed actual source;
                # require the byte-execution proof, rather than a cut timeout, to fail.
                synchronized = scratch / "ZlibF/Proof/inflate.c.match-copy.lean"
                helper_original = synchronized.read_text()
                old_helper = "  store8 l.put b"
                if helper_original.count(old_helper) != 1:
                    raise RuntimeError("MATCH helper synchronization must be unique")
                synchronized.write_text(helper_original.replace(
                    old_helper, "  store8 (← l.put.add 1) b", 1))
            result = check("ZlibF.Proof.«inflate.c." + target + "»")
            error = re.search(r"^error: ([^:\n]+):(\d+):([^\n]*)", result.stdout, re.MULTILINE)
            designated = False
            if error:
                path = Path(error.group(1))
                if path.name in proofs and path.parent == Path("ZlibF/Proof"):
                    before = (scratch / path).read_text().splitlines()[:int(error.group(2))]
                    declarations = re.findall(r"^theorem ([^\s{(]+)", "\n".join(before), re.MULTILINE)
                    designated = bool(declarations and any(
                        declarations[-1].startswith(name) for name in proofs[path.name]))
            exhausted = any(word in result.stdout.lower() for word in (
                "maximum recursion depth", "maximum number of heartbeats",
                "deterministic timeout", "deep recursion detected", "out of memory", "interrupted"))
            if result.returncode == 0 or not designated or exhausted:
                raise RuntimeError(label + " survived or failed inconclusively:\n" + result.stdout)
            print("KILLED " + label + ": " + error.group(0)
                  + "; real translation compiles; no resource failure", flush=True)
            (scratch / relative).write_text(original)
            if synchronized:
                synchronized.write_text(helper_original)
            require(check("ZlibF.Proof.«inflate.c." + target + "»"), "restored positive caller")


if __name__ == "__main__":
    main()
