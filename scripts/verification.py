#!/usr/bin/env python3
"""Check coverage, semantic locks, and final proof acceptance separately."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import shutil
import subprocess
import sys
import tempfile

import mutation_spans
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
FIXED_DIRS = (".github", "scripts", "docs/spec", "docs/api", "docs/format", "ZlibF/Runtime", "ZlibF/Zlib",
              "ZlibF/Spec", "tests", "patches")
CURRENT_LAYOUT_FILES = ("docs/README.md", "docs/design/api-model.md", "docs/design/internal-contracts.md",
                        "docs/checking/goals.md", "docs/checking/contract-review.md")


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


SPEC_LAYOUT_FILES = CURRENT_LAYOUT_FILES + (
    "docs/spec/README.md", "docs/spec/safety.md", "docs/spec/input-configurations.md",
    "docs/spec/api/README.md", "docs/spec/format/README.md")


def layout_files(manifest: dict) -> tuple[str, ...]:
    manuals = [entry["manual"].split("#", 1)[0] for entry in manifest["apis"]]
    if manuals and all(path.startswith("docs/spec/api/") for path in manuals):
        return SPEC_LAYOUT_FILES
    if manuals and all(path.startswith("docs/spec/") and
                       not path.startswith("docs/spec/api/") for path in manuals):
        return ()
    if manuals and all(path.startswith("docs/api/") for path in manuals):
        return CURRENT_LAYOUT_FILES
    raise Rejected("public manuals must use one supported documentation layout")


def public_names(header: str) -> set[str]:
    header = re.sub(r"/\*.*?\*/", "", header, flags=re.S)
    return set(re.findall(r"ZEXTERN\s+[^;]*?\bZEXPORT(?:VA)?\s+(\w+)\s*\(", header, re.S))


def source_policy() -> dict:
    paths = {ROOT / f for f in FIXED_FILES}
    manifest = json.loads((ROOT / MANIFEST).read_text())
    paths.update(ROOT / f for f in layout_files(manifest))
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


def check_versioned_sources(policy: dict) -> None:
    tracked = set(subprocess.check_output(["git", "ls-files", "-z"], cwd=ROOT,
                                          text=True).split("\0"))
    missing = set(policy["files"]) - tracked
    if missing:
        raise Rejected("locked inputs are not tracked: " + ", ".join(sorted(missing)))


def public_mutants(manifest: dict) -> dict:
    packet = json.loads((ROOT / "tests/audit/public-mutants.json").read_text())
    if set(packet) != {"version", "targets"} or packet["version"] != 1:
        raise Rejected("unknown public proof mutation manifest")
    apis = {a["goal"]: a for a in manifest["apis"] if a["scope"] == "lp64-linux"}
    targets = packet["targets"]
    if not isinstance(targets, dict) or set(targets) - set(apis):
        raise Rejected("unknown public mutation target")
    allowed = {"tests/audit/proofmut", "tests/proof-mutants", "tests/proofmut"}
    for goal, references in targets.items():
        if not isinstance(references, list) or not references:
            raise Rejected(f"no translation mutants for {goal}")
        api = apis[goal]
        source = (ROOT / api["source"]).read_text()
        start = re.search(r"^def\s+«?" + re.escape(api["function"]) + r"»?(?:\s|:)", source, re.M)
        if not start:
            raise Rejected(f"missing mutation entry: {api['function']}")
        following = re.search(r"^(?:def|theorem|abbrev|instance|structure|inductive|namespace|end)\b",
                              source[start.end():], re.M)
        end = start.end() + following.start() if following else len(source)
        body = source.find(":=", start.end(), end)
        if body < 0:
            raise Rejected(f"missing translated function body: {api['function']}")
        signature = source[start.start():body + 2]
        seen = set()
        for reference in references:
            if not isinstance(reference, dict) or set(reference) != {"list", "name"} or \
                    not isinstance(reference["name"], str) or not reference["name"]:
                raise Rejected(f"invalid mutation reference for {goal}")
            path = Path(reference["list"])
            key = (str(path), reference["name"])
            if str(path.parent) not in allowed or path.suffix != ".tsv" or key in seen:
                raise Rejected(f"invalid or duplicate mutation list for {goal}")
            seen.add(key)
            rows = [line.split("\t") for line in (ROOT / path).read_text().splitlines()
                    if line and not line.startswith("#")]
            matching = [row for row in rows if row[0] == reference["name"]]
            if len(matching) != 1 or not 5 <= len(matching[0]) <= 6:
                raise Rejected(f"missing or ambiguous mutation for {goal}: {key}")
            row = matching[0]
            old, new = row[2].replace("\\n", "\n"), row[3].replace("\\n", "\n")
            position = source.find(old)
            if row[1] != api["source"] or (len(row) == 6 and row[5]) or not row[4] or \
                    not old or old == new or source.count(old) != 1 or \
                    position < start.start() or position + len(old) > end or \
                    not source.replace(old, new).startswith(signature, start.start()):
                raise Rejected(f"mutation must change the actual function body without a gap: {goal}: {key}")
    return targets


def check_public_mutant_coverage(report: Path, manifest: dict) -> None:
    targets = public_mutants(manifest)
    public = {a["goal"] for a in manifest["apis"] if a["scope"] == "lp64-linux"}
    proved = set(re.findall(r"^goal (\S+) PROVED by ", report.read_text(), re.M))
    missing = (proved & public) - set(targets)
    if missing:
        raise Rejected("proved public targets have no function mutants: " + ", ".join(sorted(missing)))


def source_module(path: str) -> str:
    return ".".join("«" + part + "»" for part in Path(path).with_suffix("").parts)


def check_public_mutant_spans(manifest: dict) -> None:
    """Parse both source commands without loading candidate imports or executing commands."""
    targets = public_mutants(manifest)
    apis = {api["goal"]: api for api in manifest["apis"] if api["scope"] == "lp64-linux"}
    for goal, references in targets.items():
        api = apis[goal]
        original = ROOT / api["source"]
        source = original.read_text()
        for reference in references:
            row = mutation_row(reference)
            with tempfile.TemporaryDirectory(prefix="public-mutation-syntax-") as directory:
                mutant = Path(directory) / "mutant.lean"
                mutant.write_text(source.replace(row[2].replace("\\n", "\n"),
                                                 row[3].replace("\\n", "\n")))
                try:
                    mutation_spans.check(original, mutant, api["function"])
                except (ValueError, subprocess.TimeoutExpired) as error:
                    raise Rejected(f"mutation is outside the parsed function body: {goal}: {error}") from error



def mutation_row(reference: dict) -> list[str]:
    return next(line.split("\t") for line in (ROOT / reference["list"]).read_text().splitlines()
                if line and not line.startswith("#") and line.split("\t")[0] == reference["name"])


def replay_public_mutants(manifest: dict) -> None:
    """A failure in an unrelated or stronger theorem does not count."""
    targets = public_mutants(manifest)
    apis = {api["goal"]: api for api in manifest["apis"] if api["scope"] == "lp64-linux"}
    library = ROOT / ".lake/build/lib/lean"
    replay = AUDITOR_ROOT / "tests/audit/ReplayPublicProof.lean"
    registry = ROOT / "tests/audit/theorems.txt"
    for goal, references in targets.items():
        api = apis[goal]
        module = source_module(api["source"])
        command = ["lake", "env", "lean", "--run", str(replay), str(library)]
        run(command + [str(library), module, goal, str(registry)])
        for reference in references:
            row = mutation_row(reference)
            with tempfile.TemporaryDirectory(prefix="public-proof-replay-") as directory:
                candidate = Path(directory)
                shutil.copytree(ROOT / "ZlibF", candidate / "ZlibF")
                for name in ("ZlibF.lean", "lakefile.toml", "lake-manifest.json", "lean-toolchain"):
                    shutil.copyfile(ROOT / name, candidate / name)
                shutil.copytree(ROOT / ".lake", candidate / ".lake")
                path = candidate / api["source"]
                path.write_text(path.read_text().replace(row[2].replace("\\n", "\n"),
                                                        row[3].replace("\\n", "\n")))
                subprocess.run(["lake", "build", module], cwd=candidate, check=True,
                               text=True, stdout=subprocess.DEVNULL)
                result = subprocess.run(command + [str(candidate / ".lake/build/lib/lean"), module,
                                                    goal, str(registry)], cwd=ROOT,
                                        text=True, capture_output=True)
                if result.returncode != 2 or not result.stdout.startswith("EXACT_PROOF_REJECTED: "):
                    raise Rejected(f"original exact public proof survives or replay failed: {goal}: "
                                   f"{reference['name']}\n{result.stdout}{result.stderr}")
                print(f"exact public proof rejects: {goal}: {reference['name']}")


def run_public_mutants(manifest: dict) -> None:
    check_public_mutant_spans(manifest)
    replay_public_mutants(manifest)
    targets = public_mutants(manifest)
    lists = {reference["list"] for references in targets.values() for reference in references}
    lists.add("tests/proof-mutants/api-boundary.tsv")
    for path in sorted(lists):
        run(["env", "PROOFMUT_STRICT=1", "bash", "tests/audit/proofmut.sh", path])


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
    public_mutants(manifest)
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
    parser.add_argument("mode", choices=("coverage", "check", "regenerate", "specs", "mutants", "final"))
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
        manifest = coverage()
        if args.mode == "coverage":
            print("coverage is not specification readiness or proof completion")
            return 0
        if args.mode != "regenerate":
            check_versioned_sources(json.loads((ROOT / POLICY).read_text()))
        if args.mode == "mutants":
            run(["lake", "build", "ZlibF"])
            run_public_mutants(manifest)
            print("stage passed: mutants")
            return 0
        if args.mode == "final":
            run(["lake", "clean"])
        run(["lake", "build", "ZlibF"])
        check_public_mutant_spans(manifest)
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
            check_public_mutant_coverage(report, manifest)
            check_locks(report, regenerate=args.mode == "regenerate")
        policy = source_policy()
        if args.mode != "regenerate":
            check_versioned_sources(policy)
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
            replay_public_mutants(manifest)
            run(["env", f"ZLIB_SRC={ROOT / 'zlib'}", "bash", "tests/run.sh"])
            run(["env", "SAN=1", f"ZLIB_SRC={ROOT / 'zlib'}", "bash", "tests/run.sh"])
            run(["env", f"ZLIB_BUILD={ROOT / 'tests/build/zlib'}", "bash", "tests/selftest.sh"])
            mutation_lists = sorted(path for directory in
                ("tests/audit/proofmut", "tests/proof-mutants", "tests/proofmut")
                for path in (ROOT / directory).glob("*.tsv"))
            if not mutation_lists:
                raise Rejected("final acceptance requires proof mutation lists")
            for mutations in mutation_lists:
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
