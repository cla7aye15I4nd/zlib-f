#!/usr/bin/env python3
"""Check coverage, semantic locks, and final proof acceptance separately."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
AUDITOR_ROOT = ROOT
POLICY = Path("tests/audit/policy.lock")
MANIFEST = Path("tests/audit/public-api.json")
# Proof registration may grow after a semantic baseline is approved. Existing registrations
# and their types are checked against that baseline separately; goals remain source-locked.
PROOF_RECORDS = {Path("tests/audit/theorems.txt"), Path("tests/audit/statements.lock")}
FIXED_FILES = ("ZlibF.lean", "AGENTS.md", "lakefile.toml", "lean-toolchain", ".gitmodules", ".gitignore",
               "docs/safety.md", "docs/trusted-base.md", "docs/deviations.md", "docs/anti-cheating.md")
FIXED_DIRS = (".github", "scripts", "docs/spec", "ZlibF/Runtime", "ZlibF/Zlib",
              "ZlibF/Spec", "tests", "patches")


class Rejected(Exception):
    pass


def run(args: list[str], *, stdout=None) -> subprocess.CompletedProcess:
    return subprocess.run(args, cwd=ROOT, text=True, stdout=stdout, check=True)


def read_names(path: Path) -> list[str]:
    if not path.is_file() or path.is_symlink():
        raise Rejected(f"missing registry: {path}")
    names = [s.strip() for s in path.read_text().splitlines()
             if s.strip() and not s.lstrip().startswith("#")]
    if not names or len(names) != len(set(names)):
        raise Rejected(f"empty or duplicate registry: {path}")
    return names


def public_names(header: str) -> set[str]:
    header = re.sub(r"/\*.*?\*/", "", header, flags=re.S)
    return set(re.findall(r"ZEXTERN\s+[^;]*?\bZEXPORT(?:VA)?\s+(\w+)\s*\(", header, re.S))


def source_policy() -> dict:
    paths = {ROOT / f for f in FIXED_FILES}
    for directory in FIXED_DIRS:
        paths.update(p for p in (ROOT / directory).rglob("*") if p.is_file())
    paths.discard(ROOT / POLICY)
    paths.difference_update(ROOT / p for p in PROOF_RECORDS)
    paths = {p for p in paths if not ({"__pycache__", ".lake"} & set(p.relative_to(ROOT).parts))
             and p.suffix != ".pyc" and p.relative_to(ROOT).parts[:2] != ("tests", "build")}
    files = {}
    for p in sorted(paths):
        if p.is_symlink() or not p.is_file():
            raise Rejected(f"protected file missing or symlinked: {p.relative_to(ROOT)}")
        files[str(p.relative_to(ROOT))] = hashlib.sha256(p.read_bytes()).hexdigest()
    pin = subprocess.check_output(["git", "ls-files", "-s", "zlib"], cwd=ROOT, text=True).split()
    if len(pin) < 2 or pin[0] != "160000":
        raise Rejected("zlib must be a pinned submodule")
    return {"version": 1, "zlib": pin[1], "files": files}


def check_imports() -> None:
    seen: set[Path] = set()

    def visit(path: Path):
        if path in seen:
            return
        seen.add(path)
        for line in path.read_text().splitlines():
            if not line.startswith("import "):
                continue
            # A quoted component may contain dots, as in «inflate.c».
            for name in line[7:].split("--", 1)[0].split():
                local = name == "ZlibF" or name.startswith("ZlibF.")
                standard = any(name == p or name.startswith(p + ".") for p in ("Init", "Std", "Lean"))
                if not local and not standard:
                    raise Rejected(f"unapproved external module: {name}")
                parts = re.findall(r"«[^»]+»|[^.]+", name)
                child = ROOT / ("/".join(p.strip("«»") for p in parts) + ".lean")
                if child.is_file():
                    if not local:
                        raise Rejected(f"local source shadows a pinned standard module: {name}")
                    visit(child)
                elif name == "ZlibF" or name.startswith("ZlibF."):
                    raise Rejected(f"import has no source (a stale object could hide it): {name}")

    visit(ROOT / "ZlibF.lean")
    missing = set((ROOT / "ZlibF").rglob("*.lean")) - seen
    if missing:
        raise Rejected("modules outside the audited import closure: " +
                       ", ".join(str(p.relative_to(ROOT)) for p in sorted(missing)))


def coverage() -> dict:
    lake_manifest = ROOT / "lake-manifest.json"
    if lake_manifest.is_file():
        expected = {"version": "1.3.0", "packagesDir": ".lake/packages", "packages": [],
                    "name": "ZlibF", "lakeDir": ".lake", "fixedToolchain": False}
        if json.loads(lake_manifest.read_text()) != expected:
            raise Rejected("unapproved package manifest; dependencies need a reviewed policy update")
    manifest = json.loads((ROOT / MANIFEST).read_text())
    if manifest.get("version") != 1:
        raise Rejected("unknown public contract manifest version")
    expected_properties = {"documented-domain", "total-execution", "functional-result", "frame", "ownership"}
    if set(manifest.get("required_properties", [])) != expected_properties:
        raise Rejected("public contract properties are incomplete")
    apis = manifest["apis"]
    names = [a["function"] for a in apis]
    exports = public_names((ROOT / "zlib/zlib.h").read_text())
    if len(names) != len(set(names)) or set(names) != exports:
        raise Rejected(f"public API coverage differs: missing={sorted(exports - set(names))}, "
                       f"extra={sorted(set(names) - exports)}")
    pin = subprocess.check_output(["git", "-C", "zlib", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
    if pin != manifest["source_pin"] or pin != source_policy()["zlib"]:
        raise Rejected("the manifest, submodule checkout and source pin disagree")
    dirty_source = subprocess.check_output(
        ["git", "-C", "zlib", "status", "--porcelain", "--untracked-files=all"], cwd=ROOT, text=True)
    if dirty_source:
        raise Rejected("the pinned source submodule has local changes")
    goals = []
    for api in apis:
        manual, anchor = api["manual"].split("#", 1)
        for relative in (manual, api.get("source", manual)):
            path = Path(relative)
            if path.is_absolute() or ".." in path.parts or (ROOT / path).is_symlink():
                raise Rejected("public inventory paths must be ordinary repository files")
        if not re.search(r"^##\s+`?" + re.escape(api["function"]) + r"`?\s*$",
                         (ROOT / manual).read_text(), re.M) or anchor != api["function"].lower():
            raise Rejected(f"missing function contract documentation: {api['function']}")
        if api["scope"] != "lp64-linux":
            if api["function"] != "gzopen_w" or api["scope"] != "windows" or not api.get("reason"):
                raise Rejected(f"unreviewed scope exclusion: {api['function']}")
            continue
        src = (ROOT / api["source"]).read_text()
        if not re.search(r"^def\s+«?" + re.escape(api["function"]) + r"»?(?:\s|:)", src, re.M):
            raise Rejected(f"missing translated entry: {api['function']}")
        namespace = re.search(r"^namespace\s+(\S+)", src, re.M)
        if not namespace or api["implementation"] != namespace[1] + "." + api["function"]:
            raise Rejected(f"wrong translated entry binding: {api['function']}")
        if api["goal"] != "ZlibF.Spec.Public.Goal." + api["function"]:
            raise Rejected(f"wrong public contract target: {api['function']}")
        goals.append(api["goal"])
    groups = {
        "sequence_goals": ["inflate_sequence", "deflate_sequence", "inflate_back_sequence", "gz_sequence"],
        "nonvacuity_goals": ["inflate_initialisation_domain", "deflate_initialisation_domain",
                              "inflate_back_initialisation_domain", "gz_initialisation_domain"],
    }
    for group, suffixes in groups.items():
        expected = ["ZlibF.Spec.Public.Goal." + suffix for suffix in suffixes]
        if manifest.get(group) != expected:
            raise Rejected(f"missing {group}")
        goals.extend(manifest[group])
    if len(goals) != len(set(goals)):
        raise Rejected("public contracts must have distinct targets")
    check_imports()
    run([sys.executable, "scripts/gen_public_calls.py", "--check"])
    print(f"coverage: {len(exports)} public declarations, {len(goals) - 8} default-build entries, "
          "4 sequence targets, 4 initialisation-domain targets")
    return manifest


def audit(report: Path, *, strict: bool = False, public: bool = False) -> int:
    names = read_names(ROOT / "tests/audit/goals.txt")
    if public:
        manifest = coverage()
        required = [a["goal"] for a in manifest["apis"] if a["scope"] == "lp64-linux"]
        required += manifest["sequence_goals"] + manifest["nonvacuity_goals"]
        names += [name for name in required if name not in names]
    with tempfile.TemporaryDirectory(prefix="verification-goals-") as directory:
        targets = Path(directory) / "goals.txt"
        targets.write_text("\n".join(names) + "\n")
        args = ["lake", "env", "lean", "--run", str(AUDITOR_ROOT / "tests/audit/Audit.lean"),
                "tests/audit/theorems.txt", str(targets)]
        if strict:
            args.append("--require-complete")
        with report.open("w") as out:
            return subprocess.run(args, cwd=ROOT, text=True, stdout=out).returncode


def check_locks(report: Path, *, regenerate: bool = False) -> None:
    lines = report.read_text().splitlines()
    semantic = {}
    theorem_types = {}
    for line in lines:
        if line.startswith("semantic "):
            record = json.loads(line[len("semantic "):])
            if record["name"] in semantic:
                raise Rejected("duplicate semantic record")
            semantic[record["name"]] = record
        elif line.startswith("theorem-type "):
            record = json.loads(line[len("theorem-type "):])
            if record["name"] in theorem_types:
                raise Rejected("duplicate theorem-type record")
            theorem_types[record["name"]] = record["type"]

    def digest(value):
        return hashlib.sha256(json.dumps(value, ensure_ascii=True, separators=(",", ":"),
                                        sort_keys=True).encode()).hexdigest()

    trusted_names = [line.split()[1] for line in lines if line.startswith("trusted ")]
    statements = dict(line[len("statement "):].split(" :: ", 1)
                      for line in lines if line.startswith("statement "))
    if set(trusted_names) != set(semantic) or len(trusted_names) != len(semantic):
        raise Rejected("missing or duplicate full semantic records")
    if set(statements) != set(theorem_types):
        raise Rejected("missing full theorem types")
    trusted = [f"trusted {name} {digest(record['type'])} {digest(record['value'])}"
               for name, record in sorted(semantic.items())]
    types = [f"statement {name} {digest(theorem_types[name])} :: {text}"
             for name, text in sorted(statements.items())]
    for name, records in (("trusted.lock", trusted), ("statements.lock", types)):
        content = "\n".join(records) + "\n"
        if content == "\n":
            raise Rejected("empty audit report; refusing to accept or regenerate locks")
        path = ROOT / "tests/audit" / name
        if regenerate:
            path.write_text(content)
        elif not path.is_file() or path.read_text() != content:
            raise Rejected(f"semantic lock differs: {path.relative_to(ROOT)}")


def statement_records(content: str) -> dict[str, str]:
    records = {}
    for line in content.splitlines():
        if not re.fullmatch(r"statement \S+ [0-9a-f]{64} :: .+", line):
            raise Rejected("malformed statement lock")
        name, record = line[len("statement "):].split(" ", 1)
        if name in records:
            raise Rejected("duplicate statement lock")
        records[name] = record
    if not records:
        raise Rejected("empty statement lock")
    return records


def check_proof_extensions(approved_names: set[str], approved_types: dict[str, str],
                           candidate_names: set[str], candidate_types: dict[str, str]) -> None:
    if approved_names != set(approved_types) or candidate_names != set(candidate_types):
        raise Rejected("theorem registry and statement locks disagree")
    if not approved_names <= candidate_names:
        raise Rejected("an approved theorem registration was removed")
    if any(candidate_types[name] != record for name, record in approved_types.items()):
        raise Rejected("an approved theorem type changed")


def check_baseline(ref: str) -> None:
    # Resolve once. A moving branch must not select a different baseline halfway through the check.
    commit = subprocess.check_output(["git", "rev-parse", "--verify", ref + "^{commit}"],
                                     cwd=ROOT, text=True).strip()
    def approved(path: Path) -> bytes:
        return subprocess.check_output(["git", "show", f"{commit}:{path}"], cwd=ROOT)

    for path in (POLICY, Path("tests/audit/trusted.lock")):
        old = approved(path)
        if old != (ROOT / path).read_bytes():
            raise Rejected(f"proof-only baseline changed: {path}; independent semantic review required")
    theorem_path = Path("tests/audit/theorems.txt")
    statement_path = Path("tests/audit/statements.lock")
    approved_names = {line.strip() for line in approved(theorem_path).decode().splitlines()
                      if line.strip() and not line.lstrip().startswith("#")}
    check_proof_extensions(approved_names, statement_records(approved(statement_path).decode()),
                           set(read_names(ROOT / theorem_path)),
                           statement_records((ROOT / statement_path).read_text()))
    print(f"proof-only baseline: {commit}")


def main() -> int:
    global ROOT
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", choices=("coverage", "check", "regenerate", "specs", "final"))
    parser.add_argument("--baseline", help="immutable approved commit, required for final acceptance")
    parser.add_argument("--report", type=Path)
    parser.add_argument("--root", type=Path, help="candidate checkout; the auditor remains the invoking snapshot")
    args = parser.parse_args()
    if args.root:
        ROOT = args.root.resolve()
    try:
        if args.mode == "final" and not args.baseline:
            raise Rejected("final acceptance requires an approved --baseline commit")
        if args.mode == "final":
            check_baseline(args.baseline)
            if json.loads((ROOT / POLICY).read_text()) != source_policy():
                raise Rejected("candidate protected sources differ from the approved policy")
        coverage()
        if args.mode == "coverage":
            print("coverage is not specification readiness or proof completion")
            return 0
        if args.mode == "final":
            run(["lake", "clean"])
        run(["lake", "build", "ZlibF"])
        # Recheck the compiled proof terms in a fresh kernel environment, not just the build trace.
        run(["lake", "env", "leanchecker", "--fresh", "ZlibF"])
        with tempfile.TemporaryDirectory(prefix="verification-report-") as directory:
            report = args.report or Path(directory) / "audit.txt"
            rc = audit(report, strict=args.mode == "final", public=args.mode in ("specs", "final"))
            if rc:
                for line in report.read_text().splitlines():
                    if line.startswith(("goal ", "PROBLEM:")):
                        print(line)
                raise Rejected("audit rejected the requested verification stage")
            check_locks(report, regenerate=args.mode == "regenerate")
        policy = source_policy()
        if args.mode == "regenerate":
            (ROOT / POLICY).write_text(json.dumps(policy, indent=2, sort_keys=True) + "\n")
            print("regenerated locks; the diff requires independent review")
        elif not (ROOT / POLICY).is_file() or json.loads((ROOT / POLICY).read_text()) != policy:
            raise Rejected("protected source policy differs")
        if args.baseline:
            check_baseline(args.baseline)
        if args.mode == "final":
            dirty = subprocess.check_output(["git", "status", "--porcelain", "--untracked-files=normal"],
                                            cwd=ROOT, text=True)
            if dirty:
                raise Rejected("final acceptance requires a clean committed source tree")
            run(["bash", "scripts/check-sorry.sh"])
            run(["bash", "tests/audit/selftest.sh"])
            run(["env", f"ZLIB_SRC={ROOT / 'zlib'}", "bash", "tests/run.sh"])
            run(["env", "SAN=1", f"ZLIB_SRC={ROOT / 'zlib'}", "bash", "tests/run.sh"])
            run(["env", f"ZLIB_BUILD={ROOT / 'tests/build/zlib'}", "bash", "tests/selftest.sh"])
            for mutations in sorted((ROOT / "tests/audit/proofmut").glob("*.tsv")):
                run(["env", "PROOFMUT_STRICT=1", "bash", "tests/audit/proofmut.sh",
                     str(mutations.relative_to(ROOT))])
            commit = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
            print(f"final acceptance on commit: {commit}")
        print("stage passed: " + args.mode)
        if args.mode == "check":
            print("development audit only; public specification readiness and final proofs are separate gates")
        return 0
    except (Rejected, OSError, ValueError, KeyError, subprocess.CalledProcessError) as error:
        print(f"REJECTED: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
