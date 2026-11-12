#!/usr/bin/env python3
"""Check coverage, the declaration audit, proof mutants and final acceptance separately."""

from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile

import mutation_spans
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
AUDITOR_ROOT = ROOT
MANIFEST = Path("tests/audit/public-api.json")


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


UNDOCUMENTED_MARK = "/* undocumented functions (not part of the zlib API) */"


def undocumented_names(header: str) -> set[str]:
    """The exported functions zlib.h declares after its undocumented-functions comment."""
    at = header.find(UNDOCUMENTED_MARK)
    return public_names(header[at:]) if at >= 0 else set()


def required_public_goals(manifest: dict) -> list[str]:
    """The function contract goals that are required: compiled by the target and part of the zlib API.

    zlib.h declares some exported functions as undocumented and not part of the zlib API. They stay
    in the inventory, and their registered theorems stay audited, but their goals are not required.
    """
    hidden = set(manifest.get("undocumented", {}).get("functions", []))
    return [a["goal"] for a in manifest["apis"] if a["scope"] == "lp64-linux" and a["function"] not in hidden]


def mutation_apis(manifest: dict) -> dict:
    """The public functions by the goal their mutants are replayed against.

    Each function is keyed by its contract goal from the public inventory. Where the
    functional goal is not planned, its safety goal (the contract goal with the suffix
    `_safe` or `_safety`, registered in tests/audit/goals.txt) keys the same function, so
    mutants of that function are checked against the proof of its safety goal.
    """
    apis = {a["goal"]: a for a in manifest["apis"] if a["scope"] == "lp64-linux"}
    registry = ROOT / "tests/audit/goals.txt"
    registered = set(read_names(registry)) if registry.is_file() else set()
    for goal, api in list(apis.items()):
        for suffix in ("_safe", "_safety"):
            if goal + suffix in registered:
                apis.setdefault(goal + suffix, api)
    return apis


def public_mutants(manifest: dict) -> dict:
    packet = json.loads((ROOT / "tests/audit/public-mutants.json").read_text())
    if set(packet) != {"version", "targets"} or packet["version"] != 1:
        raise Rejected("unknown public proof mutation manifest")
    apis = mutation_apis(manifest)
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


def check_public_mutant_spans(manifest: dict, selected: set[str] | None = None) -> None:
    """Parse both source commands without loading candidate imports or executing commands."""
    targets = public_mutants(manifest)
    apis = mutation_apis(manifest)
    for goal, references in targets.items():
        if selected is not None and goal not in selected:
            continue
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


def copy_build_cache(source: Path, destination: Path) -> None:
    """Copy compiler artifacts, not unused native audit executables.

    The variant builds a translated module and replays through the original
    snapshot's absolute tool path. Copying its native tools into every variant
    adds large binaries that are never used. Keep all module traces and objects.
    """
    build = source.resolve() / 'build'
    shutil.copytree(source, destination, ignore=lambda path, names:
                    {'bin'} if Path(path).resolve() == build else set())


def replay_public_mutants(manifest: dict, selected: set[str] | None = None) -> None:
    """A failure in an unrelated or stronger theorem does not count."""
    targets = public_mutants(manifest)
    apis = mutation_apis(manifest)
    library = ROOT / ".lake/build/lib/lean"
    # Compile the unchanged replay program once. Each invocation still creates
    # a fresh kernel and checks the exact original registered proof closure.
    subprocess.run(['lake', 'build', 'zlibf-proof-replay'], cwd=AUDITOR_ROOT, check=True)
    replay = AUDITOR_ROOT / '.lake/build/bin/zlibf-proof-replay'
    registry = ROOT / "tests/audit/theorems.txt"
    for goal, references in targets.items():
        if selected is not None and goal not in selected:
            continue
        api = apis[goal]
        module = source_module(api["source"])
        command = ["lake", "env", str(replay), str(library)]
        run(command + [str(library), module, goal, str(registry)])
        for reference in references:
            row = mutation_row(reference)
            with tempfile.TemporaryDirectory(prefix="public-proof-replay-") as directory:
                candidate = Path(directory)
                shutil.copytree(ROOT / "ZlibF", candidate / "ZlibF")
                for name in ("ZlibF.lean", "lakefile.toml", "lake-manifest.json", "lean-toolchain"):
                    shutil.copyfile(ROOT / name, candidate / name)
                copy_build_cache(ROOT / ".lake", candidate / ".lake")
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


def mutation_partition(manifest: dict, count: int = 1, index: int = 0) -> tuple[set[str], dict[str, list[str]]]:
    """Assign every goal bundle and every full proof-list row exactly once.

    A goal's unchanged exact-proof control travels with all its public mutants.
    Full proof lists also contain cases outside the public registry. Partition
    those rows independently so none are lost or concentrated in one worker.
    """
    if count <= 0 or not 0 <= index < count:
        raise Rejected('shard count must be positive and index must be in range')
    targets = public_mutants(manifest)
    goals = {goal for ordinal, goal in enumerate(sorted(targets)) if ordinal % count == index}
    lists = {reference["list"] for references in targets.values() for reference in references}
    lists.add("tests/proof-mutants/api-boundary.tsv")
    selected = {}
    ordinal = 0
    for path in sorted(lists):
        rows = []
        for row in (ROOT / path).read_text().splitlines():
            if not row or row.startswith('#'):
                continue
            if ordinal % count == index:
                rows.append(row)
            ordinal += 1
        if rows:
            selected[path] = rows
    if not goals and not selected:
        raise Rejected('empty proof mutation shard')
    return goals, selected


def run_public_mutants(manifest: dict, count: int = 1, index: int = 0) -> None:
    goals, lists = mutation_partition(manifest, count, index)
    check_public_mutant_spans(manifest, goals)
    replay_public_mutants(manifest, goals)
    with tempfile.TemporaryDirectory(prefix='proof-mutation-shard-') as directory:
        for ordinal, (path, rows) in enumerate(lists.items()):
            subset = Path(directory) / (str(ordinal) + '-' + Path(path).name)
            subset.write_text('\n'.join(rows) + '\n')
            print(f'proof mutation shard {index}/{count}: {path}: {len(rows)} cases', flush=True)
            run(["env", "PROOFMUT_STRICT=1", "bash", "tests/audit/proofmut.sh", str(subset)])


def build_library() -> None:
    # Consumers must fail on a stale/missing artifact instead of silently doing
    # another full compile. Final acceptance retains its explicit clean build.
    flag = os.environ.get('ZLIBF_REQUIRE_PREBUILT', '0')
    if flag not in {'0', '1'}:
        raise Rejected('ZLIBF_REQUIRE_PREBUILT must be 0 or 1')
    run(['lake'] + (['--no-build'] if flag == '1' else []) + ['build', 'ZlibF'])


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
    header = (ROOT / "zlib/zlib.h").read_text()
    exports = public_names(header)
    if len(names) != len(set(names)) or set(names) != exports:
        raise Rejected(f"public API coverage differs: missing={sorted(exports - set(names))}, "
                       f"extra={sorted(set(names) - exports)}")
    undocumented = manifest.get("undocumented")
    listed = undocumented.get("functions", []) if isinstance(undocumented, dict) else []
    if not isinstance(undocumented, dict) or undocumented.get("header_comment") != UNDOCUMENTED_MARK or \
            not undocumented.get("reason") or len(listed) != len(set(listed)) or \
            set(listed) != undocumented_names(header):
        raise Rejected(f"undocumented functions differ from zlib.h: listed={sorted(listed)}, "
                       f"declared={sorted(undocumented_names(header))}")
    pin = subprocess.check_output(["git", "-C", "zlib", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
    index = subprocess.check_output(["git", "ls-files", "-s", "zlib"], cwd=ROOT, text=True).split()
    if len(index) < 2 or index[0] != "160000":
        raise Rejected("zlib must be a pinned submodule")
    if pin != manifest["source_pin"] or pin != index[1]:
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
        "safety_goals": ["inflate_sequence_safety", "deflate_sequence_safety", "uncompress_safe", "uncompress_z_safe", "uncompress2_safe", "uncompress2_z_safe", "compress_safety", "compress_z_safety", "compress2_safety", "compress2_z_safety"],
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
    print(f"coverage: {len(exports)} public declarations, "
          f"{len(goals) - 8 - len(manifest['safety_goals'])} default-build entries "
          f"({len(required_public_goals(manifest))} required, the rest undocumented in zlib.h), "
          f"4 sequence targets, 4 initialisation-domain targets, {len(manifest['safety_goals'])} safety targets")
    return manifest


def build_auditor() -> Path:
    """Compile the invoking snapshot's auditor, never a candidate-supplied tool."""
    subprocess.run(["lake", "build", "zlibf-audit"], cwd=AUDITOR_ROOT, check=True)
    return AUDITOR_ROOT / ".lake/build/bin/zlibf-audit"


def audit(report: Path, *, strict: bool = False, public: bool = False) -> int:
    names = read_names(ROOT / "tests/audit/goals.txt")
    if public:
        manifest = coverage()
        required = required_public_goals(manifest)
        required += manifest["sequence_goals"] + manifest["nonvacuity_goals"] + manifest["safety_goals"]
        names += [name for name in required if name not in names]
    with tempfile.TemporaryDirectory(prefix="verification-goals-") as directory:
        targets = Path(directory) / "goals.txt"
        targets.write_text("\n".join(names) + "\n")
        args = ["lake", "env", str(build_auditor()),
                "tests/audit/theorems.txt", str(targets)]
        if strict:
            args.append("--require-complete")
        with report.open("w") as out:
            return subprocess.run(args, cwd=ROOT, text=True, stdout=out).returncode


def main() -> int:
    global ROOT
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", choices=("coverage", "check", "specs", "mutants", "final"))
    parser.add_argument("--report", type=Path)
    parser.add_argument("--root", type=Path, help="candidate checkout; the auditor remains the invoking snapshot")
    parser.add_argument('--shard-count', type=int, default=1)
    parser.add_argument('--shard-index', type=int, default=0)
    args = parser.parse_args()
    if args.root:
        ROOT = args.root.resolve()
    try:
        if args.mode != 'mutants' and (args.shard_count, args.shard_index) != (1, 0):
            raise Rejected('sharding applies only to the mutants stage')
        manifest = coverage()
        if args.mode == "coverage":
            print("coverage is not specification readiness or proof completion")
            return 0
        if args.mode == "mutants":
            mutation_partition(manifest, args.shard_count, args.shard_index)
            build_library()
            run_public_mutants(manifest, args.shard_count, args.shard_index)
            print("stage passed: mutants")
            return 0
        if args.mode == "final":
            if os.environ.get('ZLIBF_REQUIRE_PREBUILT', '0') != '0':
                raise Rejected('final acceptance requires a clean build')
            run(["lake", "clean"])
        build_library()
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
